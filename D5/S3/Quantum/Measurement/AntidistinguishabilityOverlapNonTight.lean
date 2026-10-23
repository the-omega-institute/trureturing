/- GID: D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: AntidistinguishabilityOverlapNonTight supports the overlap bound. -/

/-
proof_shape: spectralExcess: bind-only; consumer: spectral_excess_insert, spectral_excess_monotone, spectral_failure_excess_lower, spectral_failure_fourth_bound, three_tail_excess_lower
escape_witness: spectralExcess: none
Direct frozen dependencies: spectralExcess: none
proof_shape: indexSpectral: bind-only; consumer: indexSpectral_frobSq, topThree, topThree_gram_factor, topThree_residual_frobSq, topThree_residual_psd
escape_witness: indexSpectral: none
Direct frozen dependencies: indexSpectral: none
proof_shape: indexSpectral_psd: bind-only; consumer: topThree_psd, topThree_residual_psd
escape_witness: indexSpectral_psd: none
Direct frozen dependencies: indexSpectral_psd: none
proof_shape: topThreeRows: bind-only; consumer: topThree_gram_factor, topThree_norm_square_rank, topThree_square_psd
escape_witness: topThreeRows: none
Direct frozen dependencies: topThreeRows: F20
proof_shape: sum_first_three: bind-only; consumer: topThree_gram_factor
escape_witness: sum_first_three: none
Direct frozen dependencies: sum_first_three: none
proof_shape: liftedRows: bind-only; consumer: norm_square_gram_factor, norm_square_gram_rank, topThree_square_psd
escape_witness: liftedRows: none
Direct frozen dependencies: liftedRows: F14
proof_shape: squared_modulus_lipschitz: bind-only; consumer: norm_square_lipschitz_sq
escape_witness: squared_modulus_lipschitz: none
Direct frozen dependencies: squared_modulus_lipschitz: none
proof_shape: spectral_excess_insert: bind-only; consumer: spectral_excess_monotone
escape_witness: spectral_excess_insert: none
Direct frozen dependencies: spectral_excess_insert: none
proof_shape: spectral_failure_excess_lower: bind-only; consumer: spectral_failure_fourth_bound
escape_witness: spectral_failure_excess_lower: none
Direct frozen dependencies: spectral_failure_excess_lower: none
proof_shape: indexSpectral_frobSq: bind-only; consumer: topThree_residual_frobSq
escape_witness: indexSpectral_frobSq: none
Direct frozen dependencies: indexSpectral_frobSq: F12, F13, F22
proof_shape: topThree: bind-only; consumer: quantitative_spectral_condition, topThree_diag_le, topThree_failure_distance, topThree_gram_factor, topThree_norm_square_rank, topThree_residual_frobSq, topThree_residual_psd, topThree_square_psd, topThree_square_rank
escape_witness: topThree: none
Direct frozen dependencies: topThree: F20
proof_shape: topThree_psd: bind-only; consumer: quantitative_spectral_condition
escape_witness: topThree_psd: none
Direct frozen dependencies: topThree_psd: F20
proof_shape: norm_square_gram_factor: bind-only; consumer: norm_square_gram_rank, topThree_square_psd
escape_witness: norm_square_gram_factor: none
Direct frozen dependencies: norm_square_gram_factor: F14, F28
proof_shape: norm_square_lipschitz_sq: bind-only; consumer: norm_square_frob_distance_le
escape_witness: norm_square_lipschitz_sq: none
Direct frozen dependencies: norm_square_lipschitz_sq: F8, F22
proof_shape: spectral_excess_monotone: bind-only; consumer: three_tail_excess_lower
escape_witness: spectral_excess_monotone: none
Direct frozen dependencies: spectral_excess_monotone: none
proof_shape: topThree_residual_frobSq: bind-only; consumer: topThree_failure_distance
escape_witness: topThree_residual_frobSq: none
Direct frozen dependencies: topThree_residual_frobSq: F12, F13, F20, F22
proof_shape: topThree_gram_factor: bind-only; consumer: topThree_norm_square_rank, topThree_square_psd
escape_witness: topThree_gram_factor: none
Direct frozen dependencies: topThree_gram_factor: F20
proof_shape: topThree_residual_psd: bind-only; consumer: topThree_diag_le
escape_witness: topThree_residual_psd: none
Direct frozen dependencies: topThree_residual_psd: F20
proof_shape: norm_square_gram_rank: bind-only; consumer: topThree_norm_square_rank
escape_witness: norm_square_gram_rank: none
Direct frozen dependencies: norm_square_gram_rank: F14, F15, F28
proof_shape: norm_square_frob_distance_le: bind-only; consumer: quantitative_spectral_condition
escape_witness: norm_square_frob_distance_le: none
Direct frozen dependencies: norm_square_frob_distance_le: F8, F22, F28
proof_shape: three_tail_excess_lower: bind-only; consumer: spectral_failure_fourth_bound
escape_witness: three_tail_excess_lower: none
Direct frozen dependencies: three_tail_excess_lower: none
proof_shape: topThree_norm_square_rank: bind-only; consumer: topThree_square_rank
escape_witness: topThree_norm_square_rank: none
Direct frozen dependencies: topThree_norm_square_rank: F14, F15, F20, F28
proof_shape: topThree_diag_le: bind-only; consumer: quantitative_spectral_condition
escape_witness: topThree_diag_le: none
Direct frozen dependencies: topThree_diag_le: F20
proof_shape: topThree_square_psd: bind-only; consumer: quantitative_spectral_condition
escape_witness: topThree_square_psd: none
Direct frozen dependencies: topThree_square_psd: F14, F20, F28
proof_shape: spectral_failure_fourth_bound: bind-only; consumer: quantitative_spectral_condition, spectral_failure_tail_bound
escape_witness: spectral_failure_fourth_bound: none
Direct frozen dependencies: spectral_failure_fourth_bound: none
proof_shape: topThree_square_rank: bind-only; consumer: quantitative_spectral_condition
escape_witness: topThree_square_rank: none
Direct frozen dependencies: topThree_square_rank: F14, F15, F20, F28
proof_shape: spectral_failure_tail_bound: bind-only; consumer: topThree_failure_distance
escape_witness: spectral_failure_tail_bound: none
Direct frozen dependencies: spectral_failure_tail_bound: none
proof_shape: topThree_failure_distance: bind-only; consumer: quantitative_spectral_condition
escape_witness: topThree_failure_distance: none
Direct frozen dependencies: topThree_failure_distance: F12, F13, F20, F21, F22, F24, F31, F32
proof_shape: IsTight: bind-only; consumer: claim, not_tight_of_quantitative
escape_witness: IsTight: none
Direct frozen dependencies: IsTight: none
proof_shape: not_tight_of_quantitative: bind-only; consumer: result
escape_witness: not_tight_of_quantitative: none
Direct frozen dependencies: not_tight_of_quantitative: none
proof_shape: quantitative_spectral_condition: content; consumer: quantitative_state_spectral_condition
escape_witness: quantitative_spectral_condition: quantitative_spectral_condition
Same-delivery owner dependency: quantitative_spectral_condition: F43
Direct frozen dependencies: quantitative_spectral_condition: F8, F10, F11, F12, F13, F14, F15, F19, F20, F21, F22, F23, F24, F28, F31, F32, F34, F35, F36, F38, F39, F40, F42
proof_shape: claim: bind-only; consumer: none
escape_witness: claim: none
Direct frozen dependencies: claim: none
proof_shape: quantitative_state_spectral_condition: content; consumer: quantitative_antidistinguishability
escape_witness: quantitative_state_spectral_condition: quantitative_spectral_condition
Direct frozen dependencies: quantitative_state_spectral_condition: F8, F10, F11, F12, F13, F14, F15, F19, F20, F21, F22, F23, F24, F28, F31, F32, F34, F35, F36, F38, F39, F40, F42
proof_shape: quantitative_antidistinguishability: content; consumer: result
escape_witness: quantitative_antidistinguishability: quantitative_spectral_condition
Direct frozen dependencies: quantitative_antidistinguishability: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42
proof_shape: result: content; consumer: none
escape_witness: result: quantitative_spectral_condition
Direct frozen dependencies: result: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F34, F35, F36, F37, F38, F39, F40, F41, F42
admission_basis: open-problem-resolution (#15573; Proved)
Frozen declaration identities:
F1: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse
  declaration statement_id: sha256:2a6c958072ca7dbf1881d1a83e4066dd700c1cbf16aa0e16badfd03daf7b570f
F2: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self
  declaration statement_id: sha256:5d4cb4f02e32fbc6a78b9f61a1422f801c136bab622aa301506fd1fe73fb83e3
F3: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self'
  declaration statement_id: sha256:96b5ec221bccb262c6327be49075e74bd10e17611a518a8716f2105adeba5e0a
F4: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp
  declaration statement_id: sha256:6f091bad6d67a58d7e870f0ac224732ce51ad0562376da86bee4ab6097c546cc
F5: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp'
  declaration statement_id: sha256:6e455107e336f3d6977f59a532bc341a759522fedd448aa883c77865efa182f3
F6: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse
  declaration statement_id: sha256:18736e4b1629c6ccacac40723a79c65171780f9e9f6296b93251162549f27768
F7: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.moorePenroseInverse
  declaration statement_id: sha256:d0c42c7ebe852755b1e0ac182e1eba16a13f9d7bc80db23d35a6e897dc56df5a
F8: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum
  declaration statement_id: sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
F9: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.matrix_pairing
  declaration statement_id: sha256:bc7f3a1d092a6b296a75b0e9d5c7f8c0d2698b6b92d137a30a311713b8e68880
F10: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.vectorize
  declaration statement_id: sha256:965518d7298ad8acdfeb6d0b33fc04a6e526724592513da04e49a30b340e8ddb
F11: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.vectorize_norm_sq
  declaration statement_id: sha256:6c5f3c08cd68a8eaf88971cbe045c165f849a18949357cf6c63724d4581b30e5
F12: owner GID: D5/S3/Quantum/Matrix/CommutatorGap; declaration: D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left
  baseline declaration: _private.D5.S3.Quantum.Matrix.CommutatorGap.0.D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left
  baseline declaration statement_id: sha256:d9ce203c282453198c2624036829bda9574a995fb51c1fbb98744a0940d93b8d
  current declaration statement_id: sha256:8a106b7c09f759560b1ae0469b6698029e4c2b0b2000528a314e20e06f5013ff
F13: owner GID: D5/S3/Quantum/Matrix/CommutatorGap; declaration: D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right
  declaration statement_id: sha256:63c2cd1b86c23c2972e5bf796750663ea1953eea0946f6abb48832ba5fa201e7
F14: owner GID: D5/S3/Quantum/PureState/PureStateHandshake; declaration: D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
  declaration statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
F15: owner GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound; declaration: D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap
  baseline declaration: _private.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.0.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap
  baseline declaration statement_id: sha256:3c0973d77e8d73cecffdd9c8e8632a097717e8411d9c2704171e0f19d376a740
  current declaration statement_id: sha256:c3b883a355103a5520d9e3a901baa00c984dce9232c408aa107fd385b838fb2b
F16: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration statement_id: sha256:70d3c448a772227785663f0117c0f159426907edd543b564aa470d834558dd8d
  current declaration statement_id: sha256:fa2079feef1191a452c3d4dbf8a1703c836eb544be648e3d7e26f7c50d152c41
F17: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration statement_id: sha256:e7d3fba989f8d1191d850ac68b17f943aea8d31ca3e6e460fb7f05749ab26485
  current declaration statement_id: sha256:76ab22395c4e18ba0d43115f458e8587cc482420784a2490c224e68f89700709
F18: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.PosDefOn
  declaration statement_id: sha256:9ca9d30055bd50eda8453689225e563d10cdccb3278a2b8225dc9957a0890cc7
F19: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.card_eigenvalues_reindex
  declaration statement_id: sha256:587f80758b75110c6e73f0a75200f7e8fa58b12f878eb09edb2705914a3be32b
F20: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigEquiv
  declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
F21: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigenvalues_eigEquiv
  declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
F22: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq
  declaration statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
F23: owner GID: D5/S3/Weil/ZetaLinear/RankTrace; declaration: RHLinalg.frobSq_add_hermitian
  declaration statement_id: sha256:2455ef94b9a3b384dead727978c5badae8178b7c4419a88c4ecd0cef405a3e0c
F24: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues
  declaration statement_id: sha256:8517f9a9ec34b3ab0b7f30f5025ab007ce87f585c396c39fa4b953498c3fd325
F25: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.hermForm
  declaration statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
F26: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.hermNegPart
  declaration statement_id: sha256:ad2a8390443bab24ec786ac6b42ded024195da37fd6d90578e441e73bf03e026
F27: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.negIndex
  declaration statement_id: sha256:b5905a543106ad41223ab3c0f6f31f7fb0632341c5e830350ec889bee1806429
F28: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.normSqMatrix
  declaration statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
F29: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
  declaration statement_id: sha256:10d84d7748c4e7f110f57a63c8faf31b2da6ecba24f5cdf67b5b36281d5a0757
F30: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.re_trace_mul_eq_eigenvalue_bilinear
  declaration statement_id: sha256:2f34172916d220c9b2829e523338125a57ebec289094c5be9cef75eb5b11ec2a
F31: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.rtrace
  declaration statement_id: sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F32: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.rtrace_eq_sum_eigenvalues
  declaration statement_id: sha256:7de56e963243100cb0d7ed9e3a63e24c1f7a82297129182e1158ce2a9aa88e58
F33: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.rtrace_specMap
  declaration statement_id: sha256:efa5f0bbdc4f0443275c16da086085a95c6f4e6395761aa1fadb48ed96f8ca46
F34: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap
  declaration statement_id: sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F35: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_1
  declaration statement_id: sha256:4505c32a9d334197dcdfbfe76a2b9041ae47c40d056e290040f762933ca6facf
F36: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_2
  declaration statement_id: sha256:71a8beda364a4cfc5bb497eb18cfcd54f8c12abc40e9a37962ca4f717d42c1e5
F37: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_id
  declaration statement_id: sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F38: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_isHermitian
  declaration statement_id: sha256:8eaaf395a5d8810c697d036c8729b5974aade8efbc4111a5132de5a598ab00b6
F39: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_mul
  declaration statement_id: sha256:7676c10505b22f0e9db5f08c8be82f86e9eb4db5a663554bc93b31c13a2aa6dc
F40: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.sum_eigenvalues_reindex
  declaration statement_id: sha256:6b94f504c13b3cb2a488b3b76999fcdce585f849bd38cfd344cbd8dd96c8b478
F41: owner GID: D5/S3/Weil/ZetaLinear/RankTrace; declaration: RHLinalg.trace_mul_nonneg_of_posSemidef
  declaration statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
F42: owner GID: D5/S3/Weil/ZetaLinear/VonNeumann; declaration: RHLinalg.vonNeumann_trace_ineq
  declaration statement_id: sha256:62c803a8caa4f496d67cb6aab1077ed04427bd78c6be62d5430e5aa1486bdc8e
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Published owner references use the protected baseline private declaration identities.
Same-delivery declaration in a baseline-frozen owner (pending re-pin):
F43: owner GID: D5/S3/Quantum/Matrix/CartesianVariance; declaration: D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound
  declaration statement_id: sha256:029989c48264702a7ddb2f7963b30fbc3260f0c293862ce2cf6561a7a358a67e
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module. The result Reg candidate has DTR-Undeclared.
The candidate diagnostic is IE-C050 ClosedTruthReadout: unclassified_form under
source.residual_requires_open; no source-bound escape certificate is produced.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18980
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
import D5.S3.Quantum.Measurement.OverlapLowRankDistance
import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram
open D5.S3.Quantum.Measurement.IncoherentCone
open D5.S3.Quantum.Measurement.AntidistinguishabilitySpectrum
open D5.S3.Quantum.Measurement.OverlapLowRankDistance

section
variable {ι : Type*} [DecidableEq ι]

private def spectralExcess (s : Finset ι) (x : ι → ℝ) : ℝ :=
  (∑ i ∈ s, x i) ^ 4 / 2 -
    (∑ i ∈ s, x i) ^ 2 * (∑ i ∈ s, x i ^ 2) -
    (∑ i ∈ s, x i ^ 2) ^ 2 / 2 + ∑ i ∈ s, x i ^ 4

end

section
variable {n : ℕ}

private def indexSpectral {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) hA.eigenvectorUnitary (diagonal (fun j => (v j : ℂ)))

end

section
variable {n : ℕ}

private theorem indexSpectral_psd {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) : (indexSpectral hA v).PosSemidef := by
  have hd : (diagonal (fun j => (v j : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => RCLike.ofReal_nonneg.mpr (hv j))
  exact hd.mul_mul_conjTranspose_same _

end

section
variable {n : ℕ}

private def topThreeRows {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hn : 3 ≤ n) :
    Matrix (Fin n) (Fin 3) ℂ :=
  fun i k => hA.eigenvectorUnitary i (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) (Fin.castLE hn k)) *
    (Real.sqrt ((fun k : Fin n => hA.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) (Fin.castLE hn k)) : ℂ)

end

section
variable {n : ℕ}

private theorem sum_first_three (hn : 3 ≤ n) (f : Fin n → ℂ) :
    (∑ k : Fin 3, f (Fin.castLE hn k)) = ∑ j ∈ univ.filter (fun j : Fin n => j.val < 3), f j := by
  apply sum_bij (fun k _ => Fin.castLE hn k)
  · intro k _; simp
  · intro k _ l _ hkl; exact Fin.castLE_injective hn hkl
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    exact ⟨⟨j.val, hj⟩, mem_univ _, by rfl⟩
  · intro k _; rfl

end

section
variable {n r : ℕ}

end

section
variable {n r : ℕ}

private def liftedRows (V : Matrix (Fin n) (Fin r) ℂ) :
    Matrix (Fin n) (Fin r × Fin r) ℂ :=
  fun i => Function.uncurry (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (V i))

end

section
variable {n : ℕ}

theorem squared_modulus_lipschitz (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * ‖z - w‖ := by
  calc
    |‖z‖ ^ 2 - ‖w‖ ^ 2| = |‖z‖ - ‖w‖| * (‖z‖ + ‖w‖) := by
      rw [show (‖z‖ + ‖w‖) = |‖z‖ + ‖w‖| from (abs_of_nonneg (by positivity)).symm, ← abs_mul]
      rw [show (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) = ‖z‖ ^ 2 - ‖w‖ ^ 2 by ring]
    _ ≤ ‖z - w‖ * 2 := by
      exact mul_le_mul (abs_norm_sub_norm_le z w) (by linarith)
        (by positivity) (by positivity)
    _ = 2 * ‖z - w‖ := by ring

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem spectral_excess_insert (s : Finset ι) (x : ι → ℝ) (k : ι) (hk : k ∉ s) :
    spectralExcess (insert k s) x = spectralExcess s x +
      2 * x k * ((∑ i ∈ s, x i) + x k) *
        ((∑ i ∈ s, x i) ^ 2 - (∑ i ∈ s, x i ^ 2)) := by
  simp only [spectralExcess, sum_insert hk]
  ring

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem spectral_failure_excess_lower (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (lead t bound : ℝ)
    (ht : 0 ≤ t) (hlead : lead = (∑ i ∈ s, x i) ^ 2 + t)
    (hbound : bound ≤ spectralExcess s x) :
    bound ≤ lead ^ 2 + (∑ i ∈ s, x i ^ 4) -
      (lead + ∑ i ∈ s, x i ^ 2) ^ 2 / 2 := by
  have ha : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i _ => hx i
  have hb : (∑ i ∈ s, x i ^ 2) ≤ (∑ i ∈ s, x i) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg fun i _ => hx i
  have heq : lead ^ 2 + (∑ i ∈ s, x i ^ 4) -
      (lead + ∑ i ∈ s, x i ^ 2) ^ 2 / 2 =
        spectralExcess s x + t *
          ((∑ i ∈ s, x i) ^ 2 - (∑ i ∈ s, x i ^ 2)) + t ^ 2 / 2 := by
    rw [hlead]
    unfold spectralExcess
    ring
  rw [heq]
  have hp : 0 ≤ t * ((∑ i ∈ s, x i) ^ 2 - (∑ i ∈ s, x i ^ 2)) := by positivity
  nlinarith [sq_nonneg t]

end

section
variable {n : ℕ}

private theorem indexSpectral_frobSq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (v : Fin n → ℝ) : RHLinalg.frobSq (indexSpectral hA v) = ∑ j, v j ^ 2 := by
  unfold indexSpectral
  rw [conjStarAlgAut_apply]
  change RHLinalg.frobSq ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    diagonal (fun j => (v j : ℂ)) * ((star hA.eigenvectorUnitary : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right, D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left]
  simp [RHLinalg.frobSq,  Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Complex.mul_re, sq]

end

section
variable {n : ℕ}

private def topThree {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ :=
  indexSpectral hA (fun j => if ((((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).symm j).val < 3 then hA.eigenvalues j else 0)

end

section
variable {n : ℕ}

private theorem topThree_psd {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (topThree hA.isHermitian).PosSemidef := by
  apply indexSpectral_psd
  intro j
  split_ifs <;> simp [hA.eigenvalues_nonneg]

end

section
variable {n r : ℕ}

theorem norm_square_gram_factor (V : Matrix (Fin n) (Fin r) ℂ) :
    (RHLinalg.normSqMatrix (V * Vᴴ)).map (algebraMap ℝ ℂ) =
      liftedRows V * (liftedRows V)ᴴ := by
  ext i j
  simp only [RHLinalg.normSqMatrix, Matrix.map_apply, liftedRows, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, Function.uncurry, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_mul, star_star]
  change ((‖∑ k, V i k * star (V j k)‖ ^ 2 : ℝ) : ℂ) = _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, Complex.star_def, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change star (V i l) * star (star (V j l)) * (V i k * star (V j k)) =
    V i k * star (V i l) * (V j l * star (V j k))
  rw [star_star]
  ring

end

section
variable {n : ℕ}

private theorem norm_square_lipschitz_sq (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) :
    (∑ i, ∑ j, (‖A i j‖ ^ 2 - ‖B i j‖ ^ 2) ^ 2) ≤
      4 * RHLinalg.frobSq (A - B) := by
  have hf : RHLinalg.frobSq (A - B) = ∑ i, ∑ j, ‖A i j - B i j‖ ^ 2 := by
    rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
    rw [Finset.sum_comm]
    simp only [Complex.normSq_eq_norm_sq, Matrix.sub_apply]
  rw [hf]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := squared_modulus_lipschitz (A i j) (B i j) (hA i j) (hB i j)
  have h0 : 0 ≤ |‖A i j‖ ^ 2 - ‖B i j‖ ^ 2| := abs_nonneg _
  have h1 : 0 ≤ ‖A i j - B i j‖ := norm_nonneg _
  nlinarith [sq_abs (‖A i j‖ ^ 2 - ‖B i j‖ ^ 2)]

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem spectral_excess_monotone (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    Monotone (fun s : Finset ι => spectralExcess s x) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro s k hk
  rw [spectral_excess_insert s x k hk]
  have ha : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i _ => hx i
  have hb : (∑ i ∈ s, x i ^ 2) ≤ (∑ i ∈ s, x i) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg fun i _ => hx i
  have hxk := hx k
  have hdiff := sub_nonneg.mpr hb
  have hnonneg : 0 ≤ 2 * x k * ((∑ i ∈ s, x i) + x k) *
        ((∑ i ∈ s, x i) ^ 2 - (∑ i ∈ s, x i ^ 2)) := by positivity
  linarith

end

section
variable {n : ℕ}

private theorem topThree_residual_frobSq {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hn : 4 ≤ n) :
    RHLinalg.frobSq (A - topThree hA) =
      ∑ k ∈ Ici (⟨3, by omega⟩ : Fin n), (fun k : Fin n => hA.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k ^ 2 := by
  have heq : A - topThree hA = indexSpectral hA
      (fun j => if 3 ≤ ((((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).symm j).val then hA.eigenvalues j else 0) := by
    unfold topThree indexSpectral
    conv_lhs => lhs; rw [hA.spectral_theorem]
    rw [← map_sub]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Function.comp_apply]
      split_ifs <;> first | omega | simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply]
  rw [heq, indexSpectral_frobSq]
  rw [← (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).sum_comp
    (fun j => (if 3 ≤ ((((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).symm j).val then hA.eigenvalues j else 0) ^ 2)]
  simp only [Equiv.symm_apply_apply, ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp [Fin.le_iff_val_le_val]

end

section
variable {n : ℕ}

private theorem topThree_gram_factor {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hn : 3 ≤ n) :
    topThree hA.isHermitian = topThreeRows hA.isHermitian hn * (topThreeRows hA.isHermitian hn)ᴴ := by
  ext i j
  unfold topThree indexSpectral
  rw [conjStarAlgAut_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.star_apply, topThreeRows, star_mul, RCLike.star_def, Complex.conj_ofReal]
  have hs : ∀ k, (Real.sqrt ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k) : ℂ) ^ 2 =
      ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k : ℂ) := by
    intro k
    exact_mod_cast Real.sq_sqrt (orderedSpectrum_nonneg hA k)
  have hr : (∑ k : Fin 3,
      (hA.isHermitian.eigenvectorUnitary i (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) (Fin.castLE hn k)) *
        (Real.sqrt ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) (Fin.castLE hn k)) : ℂ)) *
      ((Real.sqrt ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) (Fin.castLE hn k)) : ℂ) *
        (starRingEnd ℂ) (hA.isHermitian.eigenvectorUnitary j (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) (Fin.castLE hn k))))) =
      ∑ k : Fin 3,
        hA.isHermitian.eigenvectorUnitary i (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) (Fin.castLE hn k)) *
        ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) (Fin.castLE hn k) : ℂ) *
        star (hA.isHermitian.eigenvectorUnitary j (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) (Fin.castLE hn k))) := by
    apply sum_congr rfl
    intro k _
    change (_ * _) * (_ * star _) = _
    rw [show ∀ a b z : ℂ, (a*z)*(z*b) = a*z^2*b by intros; ring, hs]
  rw [hr, sum_first_three hn (fun k => hA.isHermitian.eigenvectorUnitary i (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k) *
    ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k : ℂ) * star (hA.isHermitian.eigenvectorUnitary j (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)))]
  rw [← (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.val < 3 <;> simp [hk]

end

section
variable {n : ℕ}

private theorem topThree_residual_psd {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    (A - topThree hA.isHermitian).PosSemidef := by
  have heq : A - topThree hA.isHermitian = indexSpectral hA.isHermitian
      (fun j => hA.isHermitian.eigenvalues j -
        if ((((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).symm j).val < 3 then hA.isHermitian.eigenvalues j else 0) := by
    unfold topThree indexSpectral
    conv_lhs => lhs; rw [hA.isHermitian.spectral_theorem]
    rw [← map_sub]
    congr 1
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply_eq, Matrix.sub_apply]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply]
  rw [heq]
  apply indexSpectral_psd
  intro j
  split_ifs <;> simp [hA.eigenvalues_nonneg]

end

section
variable {n r : ℕ}

theorem norm_square_gram_rank (V : Matrix (Fin n) (Fin r) ℂ) :
    (RHLinalg.normSqMatrix (V * Vᴴ)).rank ≤ r * r := by
  rw [← D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap
    (L := ℂ) (RHLinalg.normSqMatrix (V * Vᴴ)), norm_square_gram_factor]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa using (liftedRows V).rank_le_card_width)

end

section
variable {n : ℕ}

private theorem norm_square_frob_distance_le (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) :
    RHLinalg.frobSq ((RHLinalg.normSqMatrix A).map (algebraMap ℝ ℂ) -
      (RHLinalg.normSqMatrix B).map (algebraMap ℝ ℂ)) ≤ 4*RHLinalg.frobSq (A-B) := by
  have he : RHLinalg.frobSq ((RHLinalg.normSqMatrix A).map (algebraMap ℝ ℂ) -
      (RHLinalg.normSqMatrix B).map (algebraMap ℝ ℂ)) =
      ∑ i, ∑ j, (‖A i j‖ ^ 2 - ‖B i j‖ ^ 2) ^ 2 := by
    rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum, Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [RHLinalg.normSqMatrix, Matrix.sub_apply, Matrix.map_apply,
      Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_ofReal]
    change ‖((‖A i j‖ ^ 2 : ℝ) : ℂ) - ((‖B i j‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 = _
    rw [← Complex.ofReal_sub]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he]
  exact norm_square_lipschitz_sq A B hA hB

end

section
variable {ι : Type*} [DecidableEq ι]

private theorem three_tail_excess_lower (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (a b c : ι)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hla : ell ≤ x a) (hlb : ell ≤ x b) (hlc : ell ≤ x c) :
    12 * ell ^ 4 ≤ spectralExcess s x := by
  have hsub : ({a, b, c} : Finset ι) ⊆ s := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  have heq : spectralExcess {a, b, c} x =
      4 * x a * x b * x c * (x a + x b + x c) := by
    simp [spectralExcess, hab, hac, hbc]
    ring
  have hxa := hx a
  have hxb := hx b
  have hxc := hx c
  have hprod : ell ^ 3 ≤ x a * x b * x c := by
    calc
      ell ^ 3 = ell * ell * ell := by ring
      _ ≤ x a * x b * x c := by gcongr
  have hsum : 3 * ell ≤ x a + x b + x c := by linarith
  calc
    12 * ell ^ 4 = (4 * ell ^ 3) * (3 * ell) := by ring
    _ ≤ (4 * (x a * x b * x c)) * (x a + x b + x c) := by gcongr
    _ = spectralExcess {a, b, c} x := by rw [heq]; ring
    _ ≤ spectralExcess s x := spectral_excess_monotone x hx hsub

end

section
variable {n : ℕ}

private theorem topThree_norm_square_rank {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hn : 3 ≤ n) : (RHLinalg.normSqMatrix (topThree hA.isHermitian)).rank ≤ 9 := by
  rw [topThree_gram_factor hA hn]
  exact norm_square_gram_rank _

end

section
variable {n : ℕ}

private theorem topThree_diag_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) (i : Fin n) : (topThree hA.isHermitian i i).re ≤ 1 := by
  have hd := (Complex.nonneg_iff.mp ((topThree_residual_psd hA).diag_nonneg (i := i))).1
  change 0 ≤ (A i i - topThree hA.isHermitian i i).re at hd
  rw [Complex.sub_re, hdiag i, Complex.one_re] at hd
  linarith

end

section
variable {n : ℕ}

private theorem topThree_square_psd {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hn : 3 ≤ n) :
    ((RHLinalg.normSqMatrix (topThree hA.isHermitian)).map (algebraMap ℝ ℂ)).PosSemidef := by
  rw [topThree_gram_factor hA hn, norm_square_gram_factor]
  exact Matrix.posSemidef_self_mul_conjTranspose _

end

section


private theorem spectral_failure_fourth_bound (n : ℕ) (hn : 4 ≤ n)
    (lam : Fin n → ℝ) (hlam : ∀ k, 0 ≤ lam k) (hanti : Antitone lam)
    (hfail : (∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n), Real.sqrt (lam k)) <
      Real.sqrt (lam ⟨0, by omega⟩)) :
    12 * (lam ⟨3, by omega⟩) ^ 2 ≤
      (∑ k, (lam k) ^ 2) - (∑ k, lam k) ^ 2 / 2 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let s : Finset (Fin n) := univ.erase i0
  let x : Fin n → ℝ := fun k => Real.sqrt (lam k)
  let a : ℝ := ∑ k ∈ s, x k
  have hx : ∀ k, 0 ≤ x k := fun k => Real.sqrt_nonneg _
  have hxsq : ∀ k, x k ^ 2 = lam k := fun k => Real.sq_sqrt (hlam k)
  have hx4 : ∀ k, x k ^ 4 = lam k ^ 2 := by
    intro k
    rw [show x k ^ 4 = (x k ^ 2) ^ 2 by ring, hxsq]
  have ha : 0 ≤ a := sum_nonneg fun k _ => hx k
  have haf : a < x i0 := hfail
  have ht : 0 ≤ lam i0 - a ^ 2 := by
    have := hxsq i0
    nlinarith [hx i0]
  have hmem1 : i1 ∈ s := by simp [s, i0, i1, Fin.ext_iff]
  have hmem2 : i2 ∈ s := by simp [s, i0, i2, Fin.ext_iff]
  have hmem3 : i3 ∈ s := by simp [s, i0, i3, Fin.ext_iff]
  have hsub : 12 * x i3 ^ 4 ≤ spectralExcess s x := by
    apply three_tail_excess_lower s x hx i1 i2 i3 hmem1 hmem2 hmem3
      (by simp [i1, i2, Fin.ext_iff]) (by simp [i1, i3, Fin.ext_iff])
      (by simp [i2, i3, Fin.ext_iff]) (x i3) (hx i3)
    · exact Real.sqrt_le_sqrt (hanti (show i1 ≤ i3 by norm_num [i1, i2, i3]))
    · exact Real.sqrt_le_sqrt (hanti (show i2 ≤ i3 by norm_num [i1, i2, i3]))
    · rfl
  have hlow := spectral_failure_excess_lower s x hx (lam i0)
    (lam i0 - a ^ 2) (12 * x i3 ^ 4) ht (by dsimp [a]; ring) hsub
  have hsum : lam i0 + ∑ k ∈ s, lam k = ∑ k, lam k := by
    exact Finset.add_sum_erase univ lam (mem_univ i0)
  have hsum2 : lam i0 ^ 2 + ∑ k ∈ s, lam k ^ 2 = ∑ k, lam k ^ 2 := by
    exact Finset.add_sum_erase univ (fun k => lam k ^ 2) (mem_univ i0)
  simp only [hxsq, hx4] at hlow
  rw [hsum, hsum2] at hlow
  exact hlow

end

section
variable {n : ℕ}

private theorem topThree_square_rank {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hn : 3 ≤ n) :
    ((RHLinalg.normSqMatrix (topThree hA.isHermitian)).map (algebraMap ℝ ℂ)).rank ≤ 9 := by
  rw [D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_map_algebraMap (L := ℂ)]
  exact topThree_norm_square_rank hA hn

end

section


private theorem spectral_failure_tail_bound (n : ℕ) (hn : 4 ≤ n)
    (lam : Fin n → ℝ) (hlam : ∀ k, 0 ≤ lam k) (hanti : Antitone lam)
    (hfail : (∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n), Real.sqrt (lam k)) <
      Real.sqrt (lam ⟨0, by omega⟩)) :
    (∑ k ∈ Ici (⟨3, by omega⟩ : Fin n), lam k ^ 2) ≤
      ((n : ℝ)-3) * ((∑ k, lam k ^ 2) - (∑ k, lam k) ^ 2 / 2) / 4 := by
  let i3 : Fin n := ⟨3, by omega⟩
  let D : ℝ := (∑ k, lam k ^ 2) - (∑ k, lam k) ^ 2 / 2
  have hb : 12 * lam i3 ^ 2 ≤ D := spectral_failure_fourth_bound n hn lam hlam hanti hfail
  have hd : 0 ≤ D := (by positivity : 0 ≤ 12 * lam i3 ^ 2) |>.trans hb
  have hpt : ∀ k ∈ Ici i3, lam k ^ 2 ≤ D / 4 := by
    intro k hk
    have hk3 : i3 ≤ k := mem_Ici.mp hk
    have hs := pow_le_pow_left₀ (hlam k) (hanti hk3) 2
    nlinarith [sq_nonneg (lam i3)]
  have hsum := sum_le_sum hpt
  have hc : ((Ici i3).card : ℝ) = (n : ℝ)-3 := by
    rw [Fin.card_Ici]
    dsimp [i3]
    rw [Nat.cast_sub (by omega)]
    norm_num
  simpa only [sum_const, nsmul_eq_mul, hc, mul_div_assoc, D] using hsum

end

section
variable {n : ℕ}

private theorem topThree_failure_distance {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hn : 4 ≤ n)
    (hfail : (∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n), Real.sqrt ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k)) <
      Real.sqrt ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0, by omega⟩)) :
    RHLinalg.frobSq (A - topThree hA.isHermitian) ≤
      ((n : ℝ)-3) * (RHLinalg.frobSq A - (RHLinalg.rtrace A) ^ 2 / 2) / 4 := by
  rw [topThree_residual_frobSq hA.isHermitian hn]
  have h := spectral_failure_tail_bound n hn ((fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)))
    (orderedSpectrum_nonneg hA) (orderedSpectrum_antitone hA.isHermitian) hfail
  rw [sum_orderedSpectrum hA.isHermitian (fun x => x ^ 2),
    sum_orderedSpectrum hA.isHermitian (fun x => x)] at h
  rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hA.isHermitian,
    RHLinalg.rtrace_eq_sum_eigenvalues hA.isHermitian]
  exact h

end


section


def IsTight (n : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ (d : ℕ) (ψ : Fin n → EuclideanSpace ℂ (Fin d)),
      (∀ i, ‖ψ i‖ = 1) ∧
      (∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + ε) ∧
      ¬ IsAntidistinguishable ψ

end

section


private theorem not_tight_of_quantitative
    (n : ℕ) (hn : 10 ≤ n)
    (h : ∀ (d : ℕ) (ψ : Fin n → EuclideanSpace ℂ (Fin d)),
      (∀ i, ‖ψ i‖ = 1) →
      (∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) →
      IsAntidistinguishable ψ) : ¬ IsTight n := by
  intro ht
  obtain ⟨d, ψ, hnorm, hbound, hnot⟩ := ht (delta n) (delta_pos n hn)
  exact hnot (h d ψ hnorm hbound)

end

section


private theorem quantitative_spectral_condition (n : ℕ) (hn : 10 ≤ n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1)
    (hcap : ∀ i j, i ≠ j → ‖G i j‖ ^ 2 ≤ cSq n + delta n) :
    Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0, by omega⟩) ≤
      ∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n), Real.sqrt ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k) := by
  by_contra! hfail
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  let D : ℝ := RHLinalg.frobSq G - (n : ℝ)^2/2
  let H : Matrix (Fin n) (Fin n) ℂ := (RHLinalg.normSqMatrix G).map (algebraMap ℝ ℂ)
  let K : Matrix (Fin n) (Fin n) ℂ := (RHLinalg.normSqMatrix (topThree hG.isHermitian)).map (algebraMap ℝ ℂ)
  let H0 : Matrix (Fin n) (Fin n) ℂ := equalOverlap n (cSq n)
  have htrace : RHLinalg.rtrace G = n := by
    simp [RHLinalg.rtrace, Matrix.trace, hdiag]
  have hfourth := spectral_failure_fourth_bound n (by omega) ((fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)))
    (orderedSpectrum_nonneg hG) (orderedSpectrum_antitone hG.isHermitian) hfail
  rw [sum_orderedSpectrum hG.isHermitian (fun x => x^2),
    sum_orderedSpectrum hG.isHermitian (fun x => x),
    ← RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hG.isHermitian,
    ← RHLinalg.rtrace_eq_sum_eigenvalues hG.isHermitian, htrace] at hfourth
  have hD0 : 0 ≤ D := (by positivity : 0 ≤ 12*(fun k : Fin n => hG.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨3, by omega⟩ ^ 2) |>.trans hfourth
  have hDu : D ≤ (n : ℝ)*((n : ℝ)-1)*delta n := by
    have he := overlap_excess_identity n (by omega) G hdiag
    have hs : (∑ p ∈ ((univ : Finset (Fin n)).offDiag), (‖G p.1 p.2‖ ^ 2-cSq n)) ≤
        ∑ _p ∈ ((univ : Finset (Fin n)).offDiag), delta n := by
      apply sum_le_sum
      intro p hp
      have hne : p.1 ≠ p.2 := by simpa only [Finset.mem_offDiag, mem_univ, true_and] using hp
      linarith [hcap p.1 p.2 hne]
    rw [he] at hs
    simpa only [sum_const, nsmul_eq_mul, D5.S3.Quantum.Measurement.OverlapLowRankDistance.offDiag_card, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hs
  have hGnorm : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j
    have h := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hG i j
    rw [Complex.normSq_eq_norm_sq, hdiag i, hdiag j] at h
    norm_num only [Complex.one_re, one_mul] at h
    nlinarith [norm_nonneg (G i j)]
  have hTnorm : ∀ i j, ‖topThree hG.isHermitian i j‖ ≤ 1 := by
    intro i j
    have hT := topThree_psd hG
    have hd := topThree_diag_le hG hdiag
    have h := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hT i j
    rw [Complex.normSq_eq_norm_sq] at h
    have hj : 0 ≤ (topThree hG.isHermitian j j).re :=
      (Complex.nonneg_iff.mp (hT.diag_nonneg (i := j))).1
    have hp : (topThree hG.isHermitian i i).re *
        (topThree hG.isHermitian j j).re ≤ 1 := by
      simpa using mul_le_mul (hd i) (hd j) hj (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [norm_nonneg (topThree hG.isHermitian i j)]
  have hHK : RHLinalg.frobSq (H-K) ≤ ((n : ℝ)-9)/16 := by
    have hs := norm_square_frob_distance_le G (topThree hG.isHermitian) hGnorm hTnorm
    have ht := topThree_failure_distance hG (by omega) hfail
    rw [htrace] at ht
    have hmul := mul_le_mul_of_nonneg_left hDu (show 0 ≤ (n : ℝ)-3 by linarith)
    rw [← mul_assoc ((n : ℝ)-3) ((n : ℝ)*((n : ℝ)-1)) (delta n), delta_budget n hn] at hmul
    change RHLinalg.frobSq (H-K) ≤ _ at hs
    change RHLinalg.frobSq (G-topThree hG.isHermitian) ≤ ((n : ℝ)-3)*D/4 at ht
    nlinarith
  have hHH0 : RHLinalg.frobSq (H-H0) ≤ ((n : ℝ)-9)/64 := by
    exact (overlap_target_distance_bound n (by omega) G hdiag (delta n)
      (delta_pos n hn).le hcap hD0).trans (delta_overlap_budget n hn)
  have hH0H : RHLinalg.frobSq (H0-H) = RHLinalg.frobSq (H-H0) := by
    rw [show H0-H = -(H-H0) by abel]
    simp only [RHLinalg.frobSq, Matrix.conjTranspose_neg, neg_mul_neg]
  have hsum := frobSq_add_le_twice n (H0-H) (H-K)
  rw [show (H0-H)+(H-K) = H0-K by abel, hH0H] at hsum
  have hu : RHLinalg.frobSq (H0-K) ≤
      2*(((n : ℝ)-9)/16)+2*(((n : ℝ)-9)/64) := by linarith
  have hc0 := cSq_nonneg n (by omega)
  have hc1 := (cSq_lt_half n (by omega)).le.trans (by norm_num : (1/2 : ℝ) ≤ 1)
  have hl := equalOverlap_low_rank_distance n 9 (cSq n) hc0 hc1 K
    (topThree_square_psd hG (by omega)).isHermitian (topThree_square_rank hG (by omega))
  exact quantitative_rank_contradiction n hn (RHLinalg.frobSq (H0-K)) hu hl

end

section


def claim : Prop := ∀ n : ℕ, 10 ≤ n → ¬ IsTight n

end

section


private theorem quantitative_state_spectral_condition (n : ℕ) (hn : 10 ≤ n) (d : ℕ)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖ψ i‖ = 1)
    (hcap : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) :
    Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) ⟨0, by omega⟩) ≤
      ∑ k ∈ univ.erase (⟨0, by omega⟩ : Fin n),
        Real.sqrt ((fun k : Fin n => (gramPsd ψ).isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k) := by
  exact quantitative_spectral_condition n hn ((Matrix.gram ℂ ψ)) (gramPsd ψ)
    (stateGram_diag ψ hnorm) hcap

end

section


theorem quantitative_antidistinguishability (n : ℕ) (hn : 10 ≤ n) (d : ℕ)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖ψ i‖ = 1)
    (hcap : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ ^ 2 ≤ cSq n + delta n) :
    IsAntidistinguishable ψ := by
  apply spectral_sufficient_antidistinguishable (by omega)
  exact quantitative_state_spectral_condition n hn d ψ hnorm hcap

end

section


theorem result : claim := by
  intro n hn
  exact not_tight_of_quantitative n hn (quantitative_antidistinguishability n hn)

end

end
end D5.S3.Quantum.Measurement.AntidistinguishabilityOverlapNonTight
