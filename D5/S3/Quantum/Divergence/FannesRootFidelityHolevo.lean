/- GID: D5/S3/Quantum/Divergence/FannesRootFidelityHolevo
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/FannesRootFidelityHolevo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The three-state Holevo quantity is bounded by root-fidelity matrix entropy. -/

/-
admission_basis: open-problem-resolution (#19184; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19212.
escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product.
The source trace-log expression is inlined in holevo and claim; proofs use the frozen
ChenKatoBrandaoCMIRefutation.entropy through entropy_owner_eq_trace_log.
CanonicalRelativeModularModel is an unfrozen dev dependency, imported unchanged.
The root fidelity is inlined literally in rootFidelityMatrix; private proofs use
NMLWMeasuredFidelitySeparation.uhlmann through definitional equality.
Support inclusion is inlined as nullspace containment; matrix_log_sum translates it to
SupportAwareRelativeEntropy.SupportContained through CStarMatrix.ofMatrix.
The block algebra map composes RecordFixedAlgebraDecomposition.blockDiagonalAlgHom with
Matrix.reindexAlgEquiv, and coordinate erasure uses a row submatrix of the identity.
The block-vector helper consumes the published
D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks.mulVec_block owner;
its publication audit is recorded in this settling module and its delivery dossier.
Direct frozen dependency keys (declaration statement_id):
F1: D5/S3/Quantum/Divergence/CanonicalChannelDPI + D5.S3.Quantum.Divergence.CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi sha256:f6c41775b192518669e4da2a9dc6fbdfb3eeb83a300658a0e7df0b78458fc002
F2: D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy + D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.SupportContained sha256:b7c0cb7fe96f9bae139d3f9496d053261accc08f53f14fb5cf103b0472265047
F3: D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy + D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy sha256:a7d3bbb07eb26b884f90bdc06cc2432cb165df7624e540a62032b3647c24c54c
F4: D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy + D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_coe_of_support sha256:8a217b33805c7ccc53bf51f0fa0d5895a111ce85970b3d3beb38f5a96583a2fb
F5: D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy + D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.finiteTraceLogRelativeEntropy sha256:0261dda9a39e1f7e07275d69459038a0484f1490c01d79a8ae8b9558f3c095d9
F6: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity + D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal sha256:3a60f49e4c654be846afb7f639e5ad2ed4d5eb5fbd277586af42d3a0b6fd1809
F7: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity + D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.instNormedAlgebraComplexMatrix_d5 sha256:2fdcc8ef4caa4a8edf8b4c8e0b99524e5e9a6270887ee2ce44c0ce67c03f3c94
F8: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity + D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.instNormedRingMatrixComplex_d5 sha256:ed10e8a6fa4ad211d664e509de41111634e8ab60eb279c237f63bcae71d5f51a
F9: D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth + D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace sha256:10a7dafe6e7a6b1cf2bcce71b142fca1562280cfd40a3330284db5fc95180878
F10: D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition + D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition.blockDiagonalAlgHom sha256:8659286db7544cbf62e77e78849b85e5338b5ce326a20c0ab6636019b23a2ede
F11: D5/S3/Quantum/Foundation/FiniteKrausChannel + D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0
F12: D5/S3/Quantum/Foundation/FiniteStateChannel + D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
F13: D5/S3/Quantum/Foundation/FiniteStateChannel + D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
F14: D5/S3/Quantum/Foundation/FiniteStateChannel + D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.mapState sha256:85f38416b2caa15929825cb7cf7f1b334998a7ccc859cdb9374b371763e208d9
F15: D5/S3/Quantum/Foundation/FiniteStateChannel + D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
F16: D5/S3/Quantum/Foundation/FiniteTraceDistance + D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues sha256:e079c550fa808a0eb9281e4fd4662a1ea12091a4328d1330c268597ffc16be91
F17: D5/S3/Quantum/Foundation/FiniteTraceDistance + D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
F18: D5/S3/Quantum/Foundation/FiniteTraceDistance + D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef sha256:4f19dad9c3563d9aba3fa6f97f41f0e49ed46af1457c14f015225ae27d019565
F19: D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation + D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy sha256:979d29bab6b5d594418a43df765c4f0518bc328f8e113766e2397a9705aa4210
F20: D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation + D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy.congr_simp sha256:7d30105fd3c0679c6b161eb05a34cd90034d7688d4086671e4df99b45a3ed6b5
F21: D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation + D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy.eq_1 sha256:1635a3f2b9bd5f9de9adea9dcf5f477d6770e16adbc56312a17fe4533d1ff2af
F22: D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation + D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy_diagonal sha256:a0d6783f34a2f9ba81bfec1e48c007528e25d6b58bd5fc5790f381e6fb8549e9
F23: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation + D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann sha256:5c039d52876cf180371014477287ef2440e0e5665781b35a43cf0bccb666660b
F24: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation + D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann._proof_1 sha256:fc9e88ea1c85c86e5db621244d896cb7bb8e68d8b46c0b4c60b840dab84fedee
F25: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation + D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann._proof_2 sha256:3269172ead32ecc31bac6c79e32f36ad63e9a1b10972f60db232babed5fa2a74
F26: D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation + D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.uhlmann._proof_7 sha256:9134b1b25b4699e4623262881eb299350ce7dbb7d807a71d12bd5d2c17414596
F27: D5/S3/Quantum/Information/PartialTraceMutualInformation + D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy sha256:09c9a32f68ac5469fc76809a5425f56bb1bf01e9420bbc9a5e90fe560c195bbf
F28: D5/S3/Quantum/Information/PartialTraceMutualInformation + D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy.eq_1 sha256:dafc40abdd4836283fca9a485087835c635ff95a6fa468b105661f611488062f
F29: D5/S3/Quantum/Matrix/CartesianVariance + D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
F30: D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral + D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks.blockDiagonal_psd sha256:4f9c11415fcf94620b72c2ad955899680aeee44f6f48004203909d7793ef85f1
F31: D5/S3/Quantum/Recovery/PurifiedLocalPath + D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram sha256:0d9f33a80e1ac7a06b318c665f644b5f59c6a7e2165b62fda1db1cf395ea82e7
F32: D5/S3/Quantum/Schatten/TraceNorm + D5.S3.Quantum.Schatten.TraceNorm.traceNormUINorm sha256:307cf35ba5a0629d3d1fa7d4c63d10f667b8bf5fc722bd1c764dce53596ab632
F33: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm + D5.S3.Quantum.Schatten.UINorm.N_conjTranspose sha256:fd0d9eb501002499a309d4f4b4856825ee5ee7c092dbe102ce55393e6b048ac6
F34: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm + D5.S3.Quantum.Schatten.UINorm.unitary_invariant sha256:833a441c67b2fc4d80ca4e38001b8a4a60a92c8d4a52ad5670fcaaf32bff09f8
F35: D5/S3/QuantumBounds/PeritoTensorBlockBound + D5.S3.QuantumBounds.PeritoTensorBlockBound.unitary_diagonalization sha256:9172e2ffcb1f1eecdbf885dd50911b1254d9bf7ee6f397643e94acfba21f29d7
F36: D5/S3/Resource/LogDet/PathSpectralClassical + D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum sha256:2afdc1322560955083985858579c052c3f1e7fed0978a76f0182f08e177e3b35
F37: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.frobSq_specMap sha256:80f25164798374b84ed1f478e403177e67a5d63f6b5738ecd22c9489bb106e27
F38: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.specMap sha256:c67313b99e4225f9fcb609e9d3128cede06e325302faf08e992e27b5eb0d99de
F39: D5/S3/Weil/ZetaLinear/HermitianPosPart + RHLinalg.specMap_id sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F40: D5/S3/Weil/ZetaLinear/PosIndex + RHLinalg.frobSq sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116
Declaration classifications (consumers → prerequisite):
holevo: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo, claim, gram_entropy_accounting, holevo_eq_entropy_owner, holevo_le_blockHolevo, result, weighted_relativeEntropy_eq_holevo; Direct frozen dependencies: none.
rootFidelityMatrix: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root, claim, modulus_gram_sum, result; Direct frozen dependencies: F17.
claim: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F17.
entropy_owner_eq_trace_log: proof_shape: bind-only; escape_witness: none; consumers: entropy_eq_roots, holevo_eq_entropy_owner, modulus_sum_entropy, relativeEntropy_diagonal, relativeEntropy_eq_neg_entropy_sub_cross, result, weighted_relativeEntropy_eq_holevo; Direct frozen dependencies: F19,F21,F27,F28,F36.
holevo_eq_entropy_owner: proof_shape: bind-only; escape_witness: none; consumers: gram_entropy_accounting, weighted_relativeEntropy_eq_holevo; Direct frozen dependencies: F19,F21,F27,F28,F36.
diagonalNormSum: proof_shape: bind-only; escape_witness: none; consumers: diagonalNormSum_adjoint, diagonalNormSum_posSemidef, diagonal_attainment_adjoint, exists_traceNorm_diagonal_basis, simultaneous_matrix_decomposition, simultaneous_rank_one_decomposition; Direct frozen dependencies: none.
traceNorm_unitaries: proof_shape: bind-only; escape_witness: none; consumers: exists_traceNorm_diagonal_basis, simultaneous_matrix_decomposition; Direct frozen dependencies: F17,F32,F34.
traceNorm_adjoint: proof_shape: bind-only; escape_witness: none; consumers: diagonal_attainment_adjoint; Direct frozen dependencies: F17,F32,F33.
diagonalNormSum_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: exists_traceNorm_diagonal_basis, simultaneous_matrix_decomposition; Direct frozen dependencies: F17,F18.
exists_unitary_polar: proof_shape: bind-only; escape_witness: none; consumers: exists_traceNorm_diagonal_basis, simultaneous_matrix_decomposition; Direct frozen dependencies: F16.
unitary_diagonalization: proof_shape: bind-only; escape_witness: none; consumers: exists_traceNorm_diagonal_basis; Direct frozen dependencies: F35.
exists_traceNorm_diagonal_basis: proof_shape: bind-only; escape_witness: none; consumers: simultaneous_matrix_decomposition; Direct frozen dependencies: F16,F17,F18,F32,F34,F35.
diagonalNormSum_adjoint: proof_shape: bind-only; escape_witness: none; consumers: diagonal_attainment_adjoint; Direct frozen dependencies: none.
diagonal_attainment_adjoint: proof_shape: bind-only; escape_witness: none; consumers: simultaneous_matrix_decomposition; Direct frozen dependencies: F17,F32,F33.
simultaneous_matrix_decomposition: proof_shape: bind-only; escape_witness: none; consumers: simultaneous_rank_one_decomposition; Direct frozen dependencies: F16,F17,F18,F23,F32,F33,F34,F35.
simultaneous_rank_one_decomposition: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F16,F17,F18,F23,F32,F33,F34,F35.
relativeEntropy: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo, matrix_log_sum, modulus_sum_entropy, relativeEntropy_blockDiagonal, relativeEntropy_channel_dpi, relativeEntropy_diagonal, relativeEntropy_eq_neg_entropy_sub_cross, weighted_relativeEntropy_eq_holevo; Direct frozen dependencies: none.
relativeEntropy_eq_neg_entropy_sub_cross: proof_shape: bind-only; escape_witness: none; consumers: relativeEntropy_diagonal, weighted_relativeEntropy_eq_holevo; Direct frozen dependencies: F19,F21,F27,F28,F36.
weighted_relativeEntropy_eq_holevo: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo; Direct frozen dependencies: F19,F21,F27,F28,F36.
relativeEntropy_diagonal: proof_shape: bind-only; escape_witness: none; consumers: modulus_sum_entropy; Direct frozen dependencies: F6,F7,F8,F19,F21,F27,F28,F36.
blockHom: proof_shape: bind-only; escape_witness: none; consumers: cfc_blockDiagonal; Direct frozen dependencies: F10.
cfc_blockDiagonal: proof_shape: bind-only; escape_witness: none; consumers: relativeEntropy_blockDiagonal; Direct frozen dependencies: F10.
relativeEntropy_blockDiagonal: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: F10.
eraseKraus_action: proof_shape: bind-only; escape_witness: none; consumers: exists_eraseChannel; Direct frozen dependencies: none.
eraseKraus_complete: proof_shape: bind-only; escape_witness: none; consumers: exists_eraseChannel; Direct frozen dependencies: none.
exists_eraseChannel: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: F11,F13,F15.
supported_of_le: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo; Direct frozen dependencies: none.
supported_smul_left: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo; Direct frozen dependencies: none.
supported_diagonal: proof_shape: bind-only; escape_witness: none; consumers: modulus_sum_entropy; Direct frozen dependencies: none.
blockDiagonal_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: F30.
blockDiagonal_mulVec: proof_shape: bind-only; escape_witness: none; consumers: supported_blockDiagonal; Direct frozen dependencies: none.
supported_blockDiagonal: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: none.
density: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: F12.
relativeEntropy_channel_dpi: proof_shape: bind-only; escape_witness: none; consumers: matrix_log_sum; Direct frozen dependencies: F1,F2,F3,F4,F5,F12,F13,F14.
matrix_log_sum: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo, modulus_sum_entropy; Direct frozen dependencies: F1,F2,F3,F4,F5,F10,F11,F12,F13,F14,F15,F30.
entropy_eq_roots: proof_shape: bind-only; escape_witness: none; consumers: entropy_gram; Direct frozen dependencies: F19,F21,F27,F28,F36.
entropy_gram: proof_shape: bind-only; escape_witness: none; consumers: entropy_gram_sigma, entropy_rankOne; Direct frozen dependencies: F19,F21,F27,F28,F36.
rankOne_trace: proof_shape: bind-only; escape_witness: none; consumers: entropy_rankOne, gram_diag, vectorMass_sum; Direct frozen dependencies: F9.
entropy_rankOne: proof_shape: bind-only; escape_witness: none; consumers: gram_entropy_accounting; Direct frozen dependencies: F9,F19,F21,F22,F27,F28,F36.
columnMatrix: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root, column_mul_adjoint, diag_gram_sum, entropy_gram_sigma, gram_apply, gram_diag, gram_entropy_accounting, gram_posSemidef, gram_trace_sum, modulus_gram_sum; Direct frozen dependencies: none.
sigma: proof_shape: bind-only; escape_witness: none; consumers: column_mul_adjoint, entropy_gram_sigma, gram_entropy_accounting, holevo_le_blockHolevo, sigma_posSemidef, sigma_trace_sum, sum_sigma; Direct frozen dependencies: none.
gram_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F31.
sigma_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo; Direct frozen dependencies: none.
column_mul_adjoint: proof_shape: bind-only; escape_witness: none; consumers: entropy_gram_sigma; Direct frozen dependencies: none.
entropy_gram_sigma: proof_shape: bind-only; escape_witness: none; consumers: gram_entropy_accounting; Direct frozen dependencies: F19,F21,F27,F28,F31,F36.
gram_apply: proof_shape: bind-only; escape_witness: none; consumers: gram_diag, modulus_gram_sum; Direct frozen dependencies: F31.
gram_diag: proof_shape: bind-only; escape_witness: none; consumers: diag_gram_sum, gram_entropy_accounting, gram_trace_sum; Direct frozen dependencies: F9,F31.
blockHolevo: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root, gram_entropy_accounting, holevo_le_blockHolevo, result; Direct frozen dependencies: none.
vectorMass_sum: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F9.
sum_sigma: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo, sigma_trace_sum; Direct frozen dependencies: none.
gram_trace_sum: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F9,F31.
diag_gram_sum: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F9,F31.
gram_entropy_accounting: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F9,F19,F20,F21,F22,F27,F28,F31,F36.
modulus_gram_sum: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F17,F23,F24,F25,F26,F31.
sigma_trace_sum: proof_shape: bind-only; escape_witness: none; consumers: holevo_le_blockHolevo; Direct frozen dependencies: none.
holevo_le_blockHolevo: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F1,F2,F3,F4,F5,F10,F11,F12,F13,F14,F15,F19,F21,F27,F28,F30,F36.
diagBlock: proof_shape: bind-only; escape_witness: none; consumers: blockHolevo_le_entropy_root, diagBlock_posSemidef, modulus_sum_entropy; Direct frozen dependencies: none.
diagBlock_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: modulus_sum_entropy; Direct frozen dependencies: none.
modulus_sum_entropy: proof_shape: content; escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product; consumers: blockHolevo_le_entropy_root; Direct frozen dependencies: F1,F2,F3,F4,F5,F6,F7,F8,F10,F11,F12,F13,F14,F15,F19,F21,F27,F28,F29,F30,F36,F37,F38,F39,F40.
blockHolevo_le_entropy_root: proof_shape: content; escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product; consumers: result; Direct frozen dependencies: F1,F2,F3,F4,F5,F6,F7,F8,F9,F10,F11,F12,F13,F14,F15,F17,F19,F20,F21,F22,F23,F24,F25,F26,F27,F28,F29,F30,F31,F36,F37,F38,F39,F40.
result: proof_shape: content; escape_witness: D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_mono_product; consumers: settling result; Direct frozen dependencies: F1,F2,F3,F4,F5,F6,F7,F8,F9,F10,F11,F12,F13,F14,F15,F16,F17,F18,F19,F20,F21,F22,F23,F24,F25,F26,F27,F28,F29,F30,F31,F32,F33,F34,F35,F36,F37,F38,F39,F40.
-/

import D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy
import D5.S3.QuantumBounds.PeritoTensorBlockBound
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
import D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
import D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Schatten.TraceNorm
import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Schatten.TraceNorm
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance 3000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
open D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation (entropy entropy_diagonal)
namespace D5.S3.Quantum.Divergence.FannesRootFidelityHolevo

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

open D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation (uhlmann)

/-- Equation (2): the Holevo quantity `χ(E₃) = S(Σ_i p_i ρ_i) − Σ_i p_i S(ρ_i)` of a three-state ensemble. -/
def holevo {n : Type*} [Fintype n] [DecidableEq n]
    (p : Fin 3 → ℝ) (ρ : Fin 3 → Matrix n n ℂ) : ℝ :=
  -(Matrix.trace ((∑ i, (p i : ℂ) • ρ i) * CFC.log (∑ i, (p i : ℂ) • ρ i))).re -
    ∑ i, p i * (-(Matrix.trace (ρ i * CFC.log (ρ i))).re)

/-- The matrix `C_{√F}(E₃) = [√(p_i p_j) √F(ρ_i; ρ_j)]_{ij}` of equation (CrootFid). -/
def rootFidelityMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (p : Fin 3 → ℝ) (ρ : Fin 3 → Matrix n n ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ((Real.sqrt (p i * p j) * traceNorm (CFC.sqrt (ρ i) * CFC.sqrt (ρ j)) : ℝ) : ℂ)

/-- Conjecture 1: "For any ensemble E₃ = {(p_i, ρ_i)} with K = 3 three states of arbitrary dimension d the
corresponding Holevo quantity χ(E₃) is bounded from above by the entropy of the matrix C_{√F}(E₃)". -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (p : Fin 3 → ℝ),
    (∀ i, (ρ i).PosSemidef ∧ (ρ i).trace = 1) → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      holevo p ρ ≤ -(Matrix.trace (rootFidelityMatrix p ρ * CFC.log (rootFidelityMatrix p ρ))).re

private theorem entropy_owner_eq_trace_log {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : entropy A = -(Matrix.trace (A * CFC.log A)).re := by
  classical
  symm
  by_cases h : A.IsHermitian
  · rw [D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy, dite_eq_left h,
      entropy_eq_spectrum A h, D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy]
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  · simp only [D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy, dite_eq_right h]
    have hz : (cfc Real.log A : Matrix n n ℂ) = 0 :=
      cfc_apply_of_not_predicate A (show ¬ IsSelfAdjoint A from h)
    simp only [CFC.log, hz, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, neg_zero]

private theorem holevo_eq_entropy_owner {n : Type*} [Fintype n] [DecidableEq n]
    (p : Fin 3 → ℝ) (ρ : Fin 3 → Matrix n n ℂ) :
    holevo p ρ = entropy (∑ i, (p i : ℂ) • ρ i) - ∑ i, p i * entropy (ρ i) := by
  simp only [holevo, entropy_owner_eq_trace_log]


section
variable {n : ℕ}

private def diagonalNormSum (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ‖A i i‖

private theorem traceNorm_unitaries (A : Matrix (Fin n) (Fin n) ℂ) (U V : unitaryGroup (Fin n) ℂ) :
    traceNorm (U.val * A * V.val) = traceNorm A := by
  exact (traceNormUINorm n).unitary_invariant U.val V.val A U.prop V.prop

private theorem traceNorm_adjoint (A : Matrix (Fin n) (Fin n) ℂ) : traceNorm Aᴴ = traceNorm A := by
  exact (traceNormUINorm n).N_conjTranspose A

private theorem diagonalNormSum_posSemidef {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    diagonalNormSum A = traceNorm A := by
  have ht : traceNorm A = A.trace.re := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using
      congrArg Complex.re (traceNorm_of_posSemidef hA)
  rw [ht]
  simp only [diagonalNormSum, Matrix.trace, Matrix.diag, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hA.diag_nonneg (i := i)))).symm

private theorem exists_unitary_polar (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : unitaryGroup (Fin n) ℂ,
      (U.valᴴ * A).PosSemidef ∧ (A * U.valᴴ).PosSemidef := by
  obtain ⟨L, R, hA⟩ := exists_svd_sqrt_eigenvalues A
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (Real.sqrt
    ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) : ℂ))
  have hA' : A = L.val * D * R.valᴴ := hA
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast Real.sqrt_nonneg ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)
  let U : unitaryGroup (Fin n) ℂ := L * star R
  have hU : U.val = L.val * R.valᴴ := rfl
  refine ⟨U, ?_, ?_⟩
  · have hEq : U.valᴴ * A = R.val * D * R.valᴴ := by
      rw [hU, hA', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc L.valᴴ L.val,
        show L.valᴴ * L.val = 1 from L.prop.1, Matrix.one_mul]
    rw [hEq]
    exact hD.mul_mul_conjTranspose_same R.val
  · have hEq : A * U.valᴴ = L.val * D * L.valᴴ := by
      rw [hU, hA', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R.valᴴ R.val,
        show R.valᴴ * R.val = 1 from R.prop.1, Matrix.one_mul]
    rw [hEq]
    exact hD.mul_mul_conjTranspose_same L.val

private theorem unitary_diagonalization (U : unitaryGroup (Fin n) ℂ) :
    ∃ Q : unitaryGroup (Fin n) ℂ, ∃ z : Fin n → ℂ,
      (∀ i, ‖z i‖ = 1) ∧ Q.valᴴ * U.val * Q.val = diagonal z := by
  obtain ⟨Q, hQ, z, hz, hd⟩ :=
    D5.S3.QuantumBounds.PeritoTensorBlockBound.unitary_diagonalization U.val U.prop
  exact ⟨⟨Q, hQ⟩, z, hz, hd⟩

private theorem exists_traceNorm_diagonal_basis (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q : unitaryGroup (Fin n) ℂ,
      diagonalNormSum (Q.valᴴ * A * Q.val) = traceNorm A := by
  obtain ⟨U, hH, _⟩ := exists_unitary_polar A
  obtain ⟨Q,z,hz,hQ⟩ := unitary_diagonalization U
  let H := U.valᴴ * A
  have hB : (Q.valᴴ * H * Q.val).PosSemidef :=
    hH.conjTranspose_mul_mul_same Q.val
  have hUU : U.val * U.valᴴ = 1 := U.prop.2
  have hQQ : Q.val * Q.valᴴ = 1 := Q.prop.2
  have hfactor : Q.valᴴ * A * Q.val = diagonal z * (Q.valᴴ * H * Q.val) := by
    rw [← hQ]
    simp only [H, Matrix.mul_assoc, ← Matrix.mul_assoc Q.val Q.valᴴ,
      hQQ, Matrix.one_mul, ← Matrix.mul_assoc U.val U.valᴴ, hUU]
  refine ⟨Q, ?_⟩
  calc
    diagonalNormSum (Q.valᴴ * A * Q.val)
        = diagonalNormSum (Q.valᴴ * H * Q.val) := by
          rw [hfactor]
          simp only [diagonalNormSum, Matrix.diagonal_mul, norm_mul, hz, one_mul]
    _ = traceNorm (Q.valᴴ * H * Q.val) := diagonalNormSum_posSemidef hB
    _ = traceNorm H := traceNorm_unitaries H (star Q) Q
    _ = traceNorm A := by
      have he := traceNorm_unitaries A (star U) 1
      change traceNorm (U.valᴴ * A * 1) = traceNorm A at he
      simpa only [H, Matrix.mul_one] using he
end

section
variable {n : ℕ}

private theorem diagonalNormSum_adjoint (A : Matrix (Fin n) (Fin n) ℂ) :
    diagonalNormSum Aᴴ = diagonalNormSum A := by
  simp only [diagonalNormSum, Matrix.conjTranspose_apply, norm_star]

private theorem diagonal_attainment_adjoint {A : Matrix (Fin n) (Fin n) ℂ}
    (h : diagonalNormSum A = traceNorm A) : diagonalNormSum Aᴴ = traceNorm Aᴴ := by
  rw [diagonalNormSum_adjoint, traceNorm_adjoint, h]

private theorem simultaneous_matrix_decomposition (ρ : Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) :
    ∃ W : Fin 3 → Matrix (Fin n) (Fin n) ℂ,
      (∀ i, W i * (W i)ᴴ = ρ i) ∧
      (∀ i j, diagonalNormSum ((W i)ᴴ * W j) = uhlmann (ρ i) (ρ j)) := by
  let R : Fin 3 → Matrix (Fin n) (Fin n) ℂ := fun i => CFC.sqrt (ρ i)
  have hR (i : Fin 3) : (R i).PosSemidef := (CFC.sqrt_nonneg (ρ i)).posSemidef
  have hRstar (i : Fin 3) : (R i)ᴴ = R i := (hR i).isHermitian
  have hRsq (i : Fin 3) : R i * R i = ρ i := CFC.sqrt_mul_sqrt_self _ (hρ i).nonneg
  obtain ⟨U1, _, h01⟩ := exists_unitary_polar (R 0 * R 1)
  obtain ⟨U2, _, h02⟩ := exists_unitary_polar (R 0 * R 2)
  let U : Fin 3 → unitaryGroup (Fin n) ℂ := ![1,U1,U2]
  let A : Fin 3 → Matrix (Fin n) (Fin n) ℂ := fun i => R i * (U i).valᴴ
  obtain ⟨Q,hQ⟩ := exists_traceNorm_diagonal_basis ((A 1)ᴴ * A 2)
  let T : Fin 3 → unitaryGroup (Fin n) ℂ := fun i => star (U i) * Q
  let W : Fin 3 → Matrix (Fin n) (Fin n) ℂ := fun i => R i * (T i).val
  have hW (i : Fin 3) : W i = A i * Q.val := by
    dsimp [W,A,T]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rfl
  have hGramNorm (i j : Fin 3) : traceNorm ((W i)ᴴ * W j) = uhlmann (ρ i) (ρ j) := by
    have he : (W i)ᴴ * W j = (T i).valᴴ * (R i*R j) * (T j).val := by
      dsimp [W]
      rw [Matrix.conjTranspose_mul, hRstar]
      simp only [Matrix.mul_assoc]
    rw [he]
    exact traceNorm_unitaries (R i*R j) (star (T i)) (T j)
  have h00 (i : Fin 3) : diagonalNormSum ((W i)ᴴ * W i) = traceNorm ((W i)ᴴ*W i) :=
    diagonalNormSum_posSemidef (Matrix.posSemidef_conjTranspose_mul_self (W i))
  have h01' : ((W 0)ᴴ * W 1).PosSemidef := by
    have he : (W 0)ᴴ * W 1 = Q.valᴴ * (R 0*R 1*U1.valᴴ) * Q.val := by
      rw [hW,hW]
      simp only [A,U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, hRstar, Matrix.mul_assoc] <;> rfl
    rw [he]
    exact h01.conjTranspose_mul_mul_same Q.val
  have h02' : ((W 0)ᴴ * W 2).PosSemidef := by
    have he : (W 0)ᴴ * W 2 = Q.valᴴ * (R 0*R 2*U2.valᴴ) * Q.val := by
      rw [hW,hW]
      simp only [A,U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.conjTranspose_mul, hRstar, Matrix.mul_assoc] <;> rfl
    rw [he]
    exact h02.conjTranspose_mul_mul_same Q.val
  have h12' : diagonalNormSum ((W 1)ᴴ*W 2) = traceNorm ((W 1)ᴴ*W 2) := by
    have he : (W 1)ᴴ*W 2 = Q.valᴴ * ((A 1)ᴴ*A 2) * Q.val := by
      rw [hW,hW,Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hi := traceNorm_unitaries ((A 1)ᴴ*A 2) (star Q) Q
    change traceNorm (Q.valᴴ * ((A 1)ᴴ*A 2) * Q.val) = traceNorm ((A 1)ᴴ*A 2) at hi
    rw [he, hi]
    exact hQ
  have h10' : diagonalNormSum ((W 1)ᴴ*W 0) = traceNorm ((W 1)ᴴ*W 0) := by
    have h := diagonal_attainment_adjoint (diagonalNormSum_posSemidef h01')
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at h
    exact h
  have h20' : diagonalNormSum ((W 2)ᴴ*W 0) = traceNorm ((W 2)ᴴ*W 0) := by
    have h := diagonal_attainment_adjoint (diagonalNormSum_posSemidef h02')
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at h
    exact h
  have h21' : diagonalNormSum ((W 2)ᴴ*W 1) = traceNorm ((W 2)ᴴ*W 1) := by
    have h := diagonal_attainment_adjoint h12'
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at h
    exact h
  refine ⟨W,?_,?_⟩
  · intro i
    dsimp [W]
    rw [Matrix.conjTranspose_mul,hRstar]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (T i).val (T i).valᴴ,
      show (T i).val*(T i).valᴴ=1 from (T i).prop.2, Matrix.one_mul,hRsq]
  · intro i j
    rw [← hGramNorm]
    fin_cases i <;> fin_cases j
    · exact h00 0
    · exact diagonalNormSum_posSemidef h01'
    · exact diagonalNormSum_posSemidef h02'
    · exact h10'
    · exact h00 1
    · exact h12'
    · exact h20'
    · exact h21'
    · exact h00 2

private theorem simultaneous_rank_one_decomposition (ρ : Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) :
    ∃ v : Fin 3 → Fin n → Fin n → ℂ,
      (∀ i, ρ i = ∑ a, Matrix.vecMulVec (v i a) (star (v i a))) ∧
      (∀ i j, uhlmann (ρ i) (ρ j) =
        ∑ a, ‖star (v i a) ⬝ᵥ v j a‖) := by
  obtain ⟨W,hW,hF⟩ := simultaneous_matrix_decomposition ρ hρ
  refine ⟨fun i a k => W i k a, ?_, ?_⟩
  · intro i
    rw [← hW i]
    ext k l
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,
      Matrix.vecMulVec_apply,Pi.star_apply,starRingEnd_apply]
  · intro i j
    rw [← hF i j]
    rfl
end

section
variable {n : Type*} [Fintype n] [DecidableEq n]

private def relativeEntropy (A B : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (A*(CFC.log A-CFC.log B))).re

private theorem relativeEntropy_eq_neg_entropy_sub_cross (A B : Matrix n n ℂ) :
    relativeEntropy A B = -entropy A - (A*CFC.log B).trace.re := by
  simp only [relativeEntropy,entropy_owner_eq_trace_log,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,neg_neg]

private theorem weighted_relativeEntropy_eq_holevo (p : Fin 3 → ℝ)
    (ρ : Fin 3 → Matrix n n ℂ) :
    (∑ i, p i*relativeEntropy (ρ i) (∑ j, (p j : ℂ) • ρ j)) = holevo p ρ := by
  let M := ∑ j, (p j : ℂ) • ρ j
  have hc : (∑ i, p i * ((ρ i)*CFC.log M).trace.re) = (M*CFC.log M).trace.re := by
    dsimp [M]
    rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.smul_mul,Matrix.trace_smul]
    simp only [Complex.smul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,smul_eq_mul]
  simp_rw [relativeEntropy_eq_neg_entropy_sub_cross,mul_sub,Finset.sum_sub_distrib]
  rw [holevo_eq_entropy_owner]
  change (∑ i, p i * -entropy (ρ i)) - (∑ i, p i * ((ρ i)*CFC.log M).trace.re) =
    entropy M - ∑ i, p i * entropy (ρ i)
  rw [hc]
  simp only [mul_neg,Finset.sum_neg_distrib,entropy_owner_eq_trace_log]
  ring

private theorem relativeEntropy_diagonal (a : n → ℝ) (G : Matrix n n ℂ)
    (hdiag : ∀ i, G i i = (a i : ℂ)) :
    relativeEntropy G (Matrix.diagonal (fun i => (a i : ℂ))) =
      entropy (Matrix.diagonal (fun i => (a i : ℂ))) - entropy G := by
  have hc : (G*CFC.log (Matrix.diagonal (fun i => (a i : ℂ)))).trace =
      ((Matrix.diagonal (fun i => (a i : ℂ)))*
        CFC.log (Matrix.diagonal (fun i => (a i : ℂ)))).trace := by
    rw [cfc_log_diagonal]
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal,hdiag,Matrix.diagonal_apply_eq]
  rw [relativeEntropy_eq_neg_entropy_sub_cross,hc]
  simp only [entropy_owner_eq_trace_log]
  ring


end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private def blockHom : (ι → Matrix n n ℂ) →⋆ₐ[ℂ] Matrix (n × ι) (n × ι) ℂ := by
  let φ : (ι → Matrix n n ℂ) →ₐ[ℂ] Matrix (n × ι) (n × ι) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ
      ((Equiv.sigmaEquivProd ι n).trans (Equiv.prodComm ι n))).toAlgHom.comp
        (D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition.blockDiagonalAlgHom
          (fun _ : ι => n))
  have he : Matrix.blockDiagonal = ⇑φ := by
    exact Matrix.blockDiagonal_inj.mp rfl
  exact
    { φ.toRingHom.copy Matrix.blockDiagonal he with
      commutes' := by
        intro z
        exact (congrFun he _).trans (φ.commutes z)
      map_star' := by
        intro A
        exact (Matrix.blockDiagonal_conjTranspose A).symm }

private theorem cfc_blockDiagonal (f : ℝ → ℝ) (A : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).IsHermitian) :
    cfc f (Matrix.blockDiagonal A) = Matrix.blockDiagonal (fun a => cfc f (A a)) := by
  letI : ContinuousFunctionalCalculus ℝ (ι → Matrix n n ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have ha : IsSelfAdjoint A := Pi.isSelfAdjoint.mpr hA
  have hbd : IsSelfAdjoint (blockHom A) := ha.map _
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun a => (A a).finite_real_spectrum)).continuousOn _
  have hc : Continuous (blockHom (n := n) (ι := ι)) :=
    (blockHom (n := n) (ι := ι)).toLinearMap.continuous_of_finiteDimensional
  have hm := (blockHom (n := n) (ι := ι)).map_cfc f A hf hc ha hbd
  rw [cfc_map_pi (S := ℂ) f A (by simpa only [Pi.spectrum_eq] using hf) ha (fun a => hA a)] at hm
  exact hm.symm

private theorem relativeEntropy_blockDiagonal (A B : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hB : ∀ a, (B a).IsHermitian) :
    relativeEntropy (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      ∑ a, relativeEntropy (A a) (B a) := by
  unfold relativeEntropy CFC.log
  rw [cfc_blockDiagonal Real.log A hA, cfc_blockDiagonal Real.log B hB,
    ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul,Matrix.trace_blockDiagonal,Complex.re_sum]
  rfl

private theorem eraseKraus_action (a : ι) (X : Matrix (n × ι) (n × ι) ℂ) :
    ((((1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a)) id) * X : Matrix n (n × ι) ℂ) * ((1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a)) id)ᴴ) = X.submatrix (fun i => (i,a)) (fun i => (i,a)) := by
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change ((1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a))
    (Equiv.refl _) * X) * (1 : Matrix (n × ι) (n × ι) ℂ).submatrix
      (Equiv.refl _) (fun i => (i,a)) = _
  rw [Matrix.one_submatrix_mul _ (Equiv.refl _) X,
    Matrix.mul_submatrix_one (Equiv.refl _)]
  rfl

private theorem eraseKraus_complete : (∑ a : ι, (((1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a)) id)ᴴ * ((1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a)) id) : Matrix (n × ι) (n × ι) ℂ)) = (1 : Matrix (n × ι) (n × ι) ℂ) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Matrix.one_apply, Prod.mk.injEq, apply_ite, ite_and, eq_comm]
  split_ifs <;> simp_all

private theorem exists_eraseChannel :
    ∃ Φ : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel (n × ι) n,
      ∀ X : Matrix (n × ι) (n × ι) ℂ,
        CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          ∑ a, X.submatrix (fun i => (i,a)) (fun i => (i,a)) := by
  obtain ⟨Φ,hΦ⟩ := D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    (fun a : ι => (1 : Matrix (n × ι) (n × ι) ℂ).submatrix (fun i => (i,a)) id) eraseKraus_complete
  refine ⟨Φ,fun X => ?_⟩
  rw [hΦ]
  apply Finset.sum_congr rfl
  intro a _
  exact eraseKraus_action a X
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]


private theorem supported_of_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hAB : A ≤ B) : (∀ x, B *ᵥ x = 0 → A *ᵥ x = 0) := by
  intro x hx
  apply hA.dotProduct_mulVec_zero_iff.mp
  have hpos := (sub_nonneg.mpr hAB).posSemidef.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec,dotProduct_sub,hx,dotProduct_zero,zero_sub] at hpos
  exact le_antisymm (neg_nonneg.mp hpos) (hA.dotProduct_mulVec_nonneg x)

private theorem supported_smul_left {A B : Matrix n n ℂ} {p : ℝ} (hp : p ≠ 0)
    (h : (∀ x, B *ᵥ x = 0 → ((p : ℂ) • A) *ᵥ x = 0)) : (∀ x, B *ᵥ x = 0 → A *ᵥ x = 0) := by
  intro x hx
  have hz := h x hx
  rw [Matrix.smul_mulVec] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hp)

private theorem supported_diagonal {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (∀ x, (Matrix.diagonal (Matrix.diag A)) *ᵥ x = 0 → A *ᵥ x = 0) := by
  have hcol (j : n) (hj : A j j = 0) : ∀ i, A i j = 0 := by
    have hq : star (Pi.single j (1 : ℂ)) ⬝ᵥ A*ᵥ(Pi.single j 1) = 0 := by
      rw [Pi.star_single,star_one,Matrix.mulVec_single_one,single_one_dotProduct]
      exact hj
    have hz := hA.dotProduct_mulVec_zero_iff.mp hq
    intro i
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.zero_apply] using congrFun hz i
  intro x hx
  have hz (j : n) : A j j * x j = 0 := by
    simpa only [Matrix.mulVec_diagonal,Pi.zero_apply,Matrix.diag_apply] using congrFun hx j
  ext i
  simp only [Matrix.mulVec,dotProduct,Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  rcases mul_eq_zero.mp (hz j) with hj | hj
  · rw [hcol j hj i,zero_mul]
  · rw [hj,mul_zero]

private theorem blockDiagonal_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).PosSemidef) : (Matrix.blockDiagonal A).PosSemidef := by
  exact D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks.blockDiagonal_psd A hA

private theorem blockDiagonal_mulVec (A : ι → Matrix n n ℂ) (x : n × ι → ℂ) (i : n) (a : ι) :
    (Matrix.blockDiagonal A*ᵥx) (i,a) = (A a*ᵥ(fun j => x (j,a))) i := by
  have h :=
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks.mulVec_block
      (κ := fun _ : ι => n) A (fun y => x (y.2, y.1)) a i
  convert h using 1
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hb : a = b
  · subst b
    simp only [Matrix.blockDiagonal_apply_eq, Matrix.blockDiagonal'_apply_eq]
  · simp [Matrix.blockDiagonal_apply_ne, Matrix.blockDiagonal'_apply_ne, hb, Ne.symm hb]

private theorem supported_blockDiagonal (A B : ι → Matrix n n ℂ)
    (hs : ∀ a, (∀ x, (B a) *ᵥ x = 0 → (A a) *ᵥ x = 0)) :
    (∀ x, (Matrix.blockDiagonal B) *ᵥ x = 0 → (Matrix.blockDiagonal A) *ᵥ x = 0) := by
  intro x hx
  ext ⟨i,a⟩
  rw [blockDiagonal_mulVec]
  have hb : B a*ᵥ(fun j => x (j,a)) = 0 := by
    ext j
    simpa only [blockDiagonal_mulVec,Pi.zero_apply] using congrFun hx (j,a)
  exact congrFun (hs a _ hb) i

private def density (A : Matrix n n ℂ) (hA : A.PosSemidef) (ht : A.trace = 1) : DensityState n :=
  ⟨CStarMatrix.ofMatrix A,map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hA.nonneg,ht⟩

private theorem relativeEntropy_channel_dpi [Nonempty n] {m : Type*}
    [Fintype m] [DecidableEq m] [Nonempty m]
    (Φ : QuantumChannel n m) (ρ σ : DensityState n) (hs : SupportContained ρ σ) :
    relativeEntropy (CStarMatrix.ofMatrix.symm (Φ.mapState ρ).1)
      (CStarMatrix.ofMatrix.symm (Φ.mapState σ).1) ≤
      relativeEntropy (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1) := by
  have ho := (supported_relative_modular_model Φ ρ σ hs).outputSupport
  have h := extended_quantum_relative_entropy_channel_dpi Φ ρ σ
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support ho,
    extendedQuantumRelativeEntropy_eq_coe_of_support hs] at h
  exact WithTop.coe_le_coe.mp h
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private theorem matrix_log_sum [Nonempty n] [Nonempty ι]
    (A B : ι → Matrix n n ℂ)
    (hA : ∀ a, (A a).PosSemidef) (hB : ∀ a, (B a).PosSemidef)
    (htA : (∑ a, (A a).trace) = 1) (htB : (∑ a, (B a).trace) = 1)
    (hs : ∀ a, (∀ x, (B a) *ᵥ x = 0 → (A a) *ᵥ x = 0)) :
    relativeEntropy (∑ a, A a) (∑ a, B a) ≤ ∑ a, relativeEntropy (A a) (B a) := by
  let ρ := density (Matrix.blockDiagonal A) (blockDiagonal_posSemidef A hA)
    (by rwa [Matrix.trace_blockDiagonal])
  let σ := density (Matrix.blockDiagonal B) (blockDiagonal_posSemidef B hB)
    (by rwa [Matrix.trace_blockDiagonal])
  have hsupport : SupportContained ρ σ := by
    change ∀ ⦃x : n × ι → ℂ⦄, Matrix.blockDiagonal B *ᵥ x = 0 →
      Matrix.blockDiagonal A *ᵥ x = 0
    exact fun {x} hx => supported_blockDiagonal A B hs x hx
  obtain ⟨Φ,hΦ⟩ := exists_eraseChannel (n := n) (ι := ι)
  have hρ : CStarMatrix.ofMatrix.symm (Φ.mapState ρ).1 = ∑ a, A a := by
    change CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.blockDiagonal A))) = _
    rw [hΦ]
    congr 1
    ext a i j
    exact Matrix.blockDiagonal_apply_eq A i j a
  have hσ : CStarMatrix.ofMatrix.symm (Φ.mapState σ).1 = ∑ a, B a := by
    change CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (Matrix.blockDiagonal B))) = _
    rw [hΦ]
    congr 1
    ext a i j
    exact Matrix.blockDiagonal_apply_eq B i j a
  have h := relativeEntropy_channel_dpi Φ ρ σ hsupport
  rw [hρ,hσ] at h
  change relativeEntropy (∑ a, A a) (∑ a, B a) ≤
    relativeEntropy (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) at h
  rwa [relativeEntropy_blockDiagonal A B (fun a => (hA a).isHermitian)
    (fun a => (hB a).isHermitian)] at h
end

section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem entropy_eq_roots (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    entropy A = (A.charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  rw [entropy_owner_eq_trace_log, entropy_eq_spectrum A hA,hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map,Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re]
  change -(∑ i,hA.eigenvalues i*Real.log (hA.eigenvalues i)) =
    ∑ i,Real.negMulLog (hA.eigenvalues i)
  simp [Real.negMulLog,Finset.sum_neg_distrib]

private theorem entropy_gram (V : Matrix n m ℂ) : entropy (Vᴴ*V) = entropy (V*Vᴴ) := by
  have h := congrArg
    (fun p : Polynomial ℂ => (p.roots.map (fun z => Real.negMulLog z.re)).sum)
    (Matrix.charpoly_mul_comm' Vᴴ V)
  simpa [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero,
    Polynomial.roots_X_pow, Multiset.nsmul_singleton, Multiset.map_replicate,
    entropy_eq_roots _ (Matrix.isHermitian_conjTranspose_mul_self V),
    entropy_eq_roots _ (Matrix.isHermitian_mul_conjTranspose_self V)] using h


private theorem rankOne_trace (v : n → ℂ) : ((Matrix.vecMulVec v (star v))).trace = ((‖WithLp.toLp 2 v‖^2 : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_pow] using
    D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace (WithLp.toLp 2 v)

private theorem entropy_rankOne (v : n → ℂ) : entropy ((Matrix.vecMulVec v (star v))) = Real.negMulLog ((‖WithLp.toLp 2 v‖^2 : ℝ)) := by
  let V : Matrix n Unit ℂ := fun i _ => v i
  have he : V*Vᴴ = (Matrix.vecMulVec v (star v)) := by
    ext i j
    simp [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,Pi.star_apply]
  have hg : Vᴴ*V = Matrix.diagonal (fun _ : Unit => ((‖WithLp.toLp 2 v‖^2 : ℝ) : ℂ)) := by
    ext i j
    have ht := rankOne_trace v
    simpa [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.trace,Matrix.diag,
      Matrix.vecMulVec_apply,Pi.star_apply,mul_comm] using ht
  rw [← he,← entropy_gram V,hg,entropy_diagonal]
  simp
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private def columnMatrix (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ) (a : ι) : Matrix n (Fin 3) ℂ :=
  fun k i => (Real.sqrt (p i) : ℂ)*v i a k

private def sigma (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ) (a : ι) : Matrix n n ℂ :=
  ∑ i, (p i : ℂ) • (Matrix.vecMulVec (v i a) (star (v i a)))

private theorem gram_posSemidef (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ) (a : ι) :
    (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

private theorem sigma_posSemidef (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (a : ι) : (sigma p v a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hp i)

private theorem column_mul_adjoint (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (a : ι) :
    columnMatrix p v a*(columnMatrix p v a)ᴴ = sigma p v a := by
  ext k l
  simp only [columnMatrix,sigma,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Pi.star_apply,
    star_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (Real.sqrt (p i) : ℂ)*(Real.sqrt (p i) : ℂ) = (p i : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hp i)
  calc
    _ = ((Real.sqrt (p i) : ℂ)*(Real.sqrt (p i) : ℂ))*(v i a k*star (v i a l)) := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hs]; rfl

private theorem entropy_gram_sigma (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (a : ι) : entropy (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)) = entropy (sigma p v a) := by
  rw [D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram,entropy_gram,column_mul_adjoint p hp]

private theorem gram_apply (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ) (a : ι) (i j : Fin 3) :
    D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i j = ((Real.sqrt (p i)*Real.sqrt (p j) : ℝ) : ℂ) *
      (star (v i a) ⬝ᵥ v j a) := by
  simp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram,columnMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_mul,Complex.star_def,Complex.conj_ofReal,dotProduct,Pi.star_apply,
    Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem gram_diag (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (a : ι) (i : Fin 3) :
    D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i i = ((p i*(‖WithLp.toLp 2 (v i a)‖^2 : ℝ) : ℝ) : ℂ) := by
  rw [gram_apply,Real.mul_self_sqrt (hp i)]
  have hq : star (v i a) ⬝ᵥ v i a = ((‖WithLp.toLp 2 (v i a)‖^2 : ℝ) : ℂ) := by
    have h := rankOne_trace (v i a)
    simpa [Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,dotProduct,mul_comm] using h
  rw [hq,Complex.ofReal_mul]
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private def blockHolevo (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ) : ℝ :=
  ∑ a, holevo p (fun i => (Matrix.vecMulVec (v i a) (star (v i a))))

private theorem vectorMass_sum (v : Fin 3 → ι → n → ℂ)
    (ρ : Fin 3 → Matrix n n ℂ) (hρ : ∀ i,ρ i=∑ a,(Matrix.vecMulVec (v i a) (star (v i a))))
    (ht : ∀ i,(ρ i).trace=1) (i : Fin 3) : ∑ a,(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)=1 := by
  have h := ht i
  rw [hρ i,Matrix.trace_sum] at h
  simp_rw [rankOne_trace] at h
  exact_mod_cast h

private theorem sum_sigma (p : Fin 3 → ℝ) (v : Fin 3 → ι → n → ℂ)
    (ρ : Fin 3 → Matrix n n ℂ) (hρ : ∀ i,ρ i=∑ a,(Matrix.vecMulVec (v i a) (star (v i a)))) :
    (∑ a,sigma p v a)=∑ i,(p i : ℂ) • ρ i := by
  simp only [sigma,hρ,Finset.smul_sum]
  exact Finset.sum_comm

private theorem gram_trace_sum (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (v : Fin 3 → ι → n → ℂ) (hq : ∀ i,∑ a,(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)=1) :
    (∑ a,(D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)).trace)=1 := by
  simp only [Matrix.trace,Matrix.diag,gram_diag p hp,← Complex.ofReal_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,hq,mul_one,hs,Complex.ofReal_one]

private theorem diag_gram_sum (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (hq : ∀ i,∑ a,(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)=1) :
    (∑ a,Matrix.diagonal (fun i => (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i i))) =
      Matrix.diagonal (fun i => (p i : ℂ)) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.sum_apply,Matrix.diagonal_apply_eq,gram_diag p hp,
      ← Complex.ofReal_sum,← Finset.mul_sum,hq,mul_one]
  · simp [Matrix.sum_apply,Matrix.diagonal_apply,hij]

private theorem gram_entropy_accounting (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (hq : ∀ i,∑ a,(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)=1) :
    (∑ a,entropy (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a))) -
      (∑ a,entropy (Matrix.diagonal (fun i => D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i i))) +
      entropy (Matrix.diagonal (fun i => (p i : ℂ))) = blockHolevo p v := by
  have hdiag (a : ι) : entropy (Matrix.diagonal (fun i => D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i i)) =
      ∑ i,Real.negMulLog (p i)*(‖WithLp.toLp 2 (v i a)‖^2 : ℝ) +
        ∑ i,p i*entropy ((Matrix.vecMulVec (v i a) (star (v i a)))) := by
    simp_rw [gram_diag p hp]
    rw [entropy_diagonal]
    simp_rw [Real.negMulLog_mul,entropy_rankOne]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [entropy_gram_sigma p hp,hdiag]
  rw [Finset.sum_add_distrib,entropy_diagonal]
  have hclass : (∑ a,∑ i,Real.negMulLog (p i)*(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)) =
      ∑ i,Real.negMulLog (p i) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,hq,mul_one]
  rw [hclass]
  unfold blockHolevo
  simp_rw [holevo_eq_entropy_owner]
  change (∑ a,entropy (sigma p v a)) -
      ((∑ i,Real.negMulLog (p i)) + (∑ a,∑ i,p i*entropy ((Matrix.vecMulVec (v i a) (star (v i a)))))) +
      (∑ i,Real.negMulLog (p i)) = _
  rw [Finset.sum_sub_distrib]
  simp only [sigma]
  ring

private theorem modulus_gram_sum (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i)
    (v : Fin 3 → ι → n → ℂ) (ρ : Fin 3 → Matrix n n ℂ)
    (hF : ∀ i j,uhlmann (ρ i) (ρ j)=∑ a,‖star (v i a) ⬝ᵥ v j a‖) :
    (∑ a,entryModulus (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)))=rootFidelityMatrix p ρ := by
  ext i j
  simp only [Matrix.sum_apply,entryModulus,Matrix.map_apply,gram_apply,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    rootFidelityMatrix,← Complex.ofReal_sum,← Finset.mul_sum,← hF,uhlmann]
  rw [Real.sqrt_mul (hp i)]
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private theorem sigma_trace_sum (p : Fin 3 → ℝ) (hs : ∑ i,p i=1)
    (v : Fin 3 → ι → n → ℂ) (ρ : Fin 3 → Matrix n n ℂ)
    (hρ : ∀ i,ρ i=∑ a,(Matrix.vecMulVec (v i a) (star (v i a)))) (ht : ∀ i,(ρ i).trace=1) :
    (∑ a,(sigma p v a).trace)=1 := by
  rw [← Matrix.trace_sum,sum_sigma p v ρ hρ,Matrix.trace_sum]
  simp only [Matrix.trace_smul,ht,smul_eq_mul,mul_one,← Complex.ofReal_sum,hs,Complex.ofReal_one]

private theorem holevo_le_blockHolevo [Nonempty n] [Nonempty ι]
    (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (v : Fin 3 → ι → n → ℂ) (ρ : Fin 3 → Matrix n n ℂ)
    (hρ : ∀ i,ρ i=∑ a,(Matrix.vecMulVec (v i a) (star (v i a)))) (ht : ∀ i,(ρ i).trace=1) :
    holevo p ρ ≤ blockHolevo p v := by
  have hpair (i : Fin 3) :
      p i*relativeEntropy (ρ i) (∑ j,(p j : ℂ) • ρ j) ≤
      p i*(∑ a,relativeEntropy ((Matrix.vecMulVec (v i a) (star (v i a)))) (sigma p v a)) := by
    by_cases hz : p i=0
    · simp [hz]
    · have hsupport (a : ι) : (∀ x, (sigma p v a) *ᵥ x = 0 → ((Matrix.vecMulVec (v i a) (star (v i a)))) *ᵥ x = 0) := by
        apply supported_smul_left hz
        apply supported_of_le
        · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hp i)
        · exact Finset.single_le_sum (fun j _ =>
            ((Matrix.posSemidef_vecMulVec_self_star (v j a)).smul (by exact_mod_cast hp j)).nonneg)
            (Finset.mem_univ i)
      have hA : (∑ a,((Matrix.vecMulVec (v i a) (star (v i a)))).trace)=1 := by
        rw [← Matrix.trace_sum,← hρ i]
        exact ht i
      have h := matrix_log_sum (fun a => (Matrix.vecMulVec (v i a) (star (v i a)))) (sigma p v)
        (fun a => Matrix.posSemidef_vecMulVec_self_star _) (sigma_posSemidef p hp v) hA
        (sigma_trace_sum p hs v ρ hρ ht) hsupport
      rw [← hρ i,sum_sigma p v ρ hρ] at h
      exact mul_le_mul_of_nonneg_left h (hp i)
  rw [← weighted_relativeEntropy_eq_holevo p ρ]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpair i)
  refine h.trans_eq ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold blockHolevo
  apply Finset.sum_congr rfl
  intro a _
  exact weighted_relativeEntropy_eq_holevo p (fun i => (Matrix.vecMulVec (v i a) (star (v i a))))
end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private def diagBlock (G : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => (‖G i i‖ : ℂ))

private theorem diagBlock_posSemidef (G : Matrix (Fin 3) (Fin 3) ℂ) : (diagBlock G).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast norm_nonneg (G i i)

private theorem modulus_sum_entropy (G : ι → Matrix (Fin 3) (Fin 3) ℂ)
    (hG : ∀ a,(G a).PosSemidef) (ht : (∑ a,(G a).trace)=1) :
    (∑ a, entropy (G a)) - (∑ a, entropy (diagBlock (G a))) +
      entropy (∑ a,diagBlock (G a)) ≤ entropy (∑ a,entryModulus (G a)) := by
  let K := fun a => entryModulus (G a)
  let D := fun a => diagBlock (G a)
  have hK (a : ι) : (K a).PosSemidef := entryModulus_posSemidef (hG a)
  have hD (a : ι) : (D a).PosSemidef := diagBlock_posSemidef (G a)
  have htK : (∑ a,(K a).trace)=1 := by
    exact (Finset.sum_congr rfl (fun a _ => entryModulus_trace (hG a))).trans ht
  have htrD (a : ι) : (D a).trace = (K a).trace := by
    exact Complex.ext rfl rfl
  have htD : (∑ a,(D a).trace)=1 := by
    exact (Finset.sum_congr rfl (fun a _ => htrD a)).trans htK
  have hs (a : ι) : (∀ x, (D a) *ᵥ x = 0 → (K a) *ᵥ x = 0) := supported_diagonal (hK a)
  have hls := matrix_log_sum K D hK hD htK htD hs
  have hcmp (a : ι) : relativeEntropy (K a) (D a) ≤ relativeEntropy (G a) (D a) := by
    dsimp only [K,D,diagBlock]
    rw [relativeEntropy_diagonal (fun i => ‖G a i i‖) (entryModulus (G a)) (fun _ => rfl),
      relativeEntropy_diagonal (fun i => ‖G a i i‖) (G a)
        (fun i => (entryModulus_diag (hG a) i).symm)]
    apply sub_le_sub_left
    simpa only [entropy_owner_eq_trace_log] using entryModulus_entropy_mono (hG a)
  have htot : ∑ a,D a = Matrix.diagonal (fun i => ((∑ a,‖G a i i‖ : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [D,diagBlock,Matrix.sum_apply,Matrix.diagonal_apply]
    · simp [D,diagBlock,Matrix.sum_apply,Matrix.diagonal_apply,hij]
  have hdiag (i : Fin 3) : (∑ a,K a) i i = ((∑ a,‖G a i i‖ : ℝ) : ℂ) := by
    simp [K,entryModulus,Matrix.sum_apply]
  have hcross : relativeEntropy (∑ a,K a) (∑ a,D a) =
      entropy (∑ a,D a) - entropy (∑ a,K a) := by
    rw [htot]
    exact relativeEntropy_diagonal _ _ hdiag
  have hGrel (a : ι) : relativeEntropy (G a) (D a) = entropy (D a)-entropy (G a) :=
    relativeEntropy_diagonal _ _ (fun i => (entryModulus_diag (hG a) i).symm)
  have hle := hls.trans (Finset.sum_le_sum (fun a _ => hcmp a))
  rw [hcross] at hle
  simp_rw [hGrel] at hle
  rw [Finset.sum_sub_distrib] at hle
  dsimp [K,D] at hle
  linarith
end

section
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem blockHolevo_le_entropy_root (p : Fin 3 → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (v : Fin 3 → ι → n → ℂ) (ρ : Fin 3 → Matrix n n ℂ)
    (hq : ∀ i,∑ a,(‖WithLp.toLp 2 (v i a)‖^2 : ℝ)=1)
    (hF : ∀ i j,uhlmann (ρ i) (ρ j)=∑ a,‖star (v i a) ⬝ᵥ v j a‖) :
    blockHolevo p v ≤ entropy (rootFidelityMatrix p ρ) := by
  have hd (a : ι) : diagBlock (D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)) = Matrix.diagonal (fun i => D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a) i i) := by
    unfold diagBlock
    congr 1
    ext i
    exact entryModulus_diag (gram_posSemidef p v a) i
  have h := modulus_sum_entropy (fun a => D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (columnMatrix p v a)) (gram_posSemidef p v) (gram_trace_sum p hp hs v hq)
  simp_rw [hd] at h
  rw [diag_gram_sum p hp v hq,gram_entropy_accounting p hp v hq,
    modulus_gram_sum p hp v ρ hF] at h
  exact h
end

theorem result : claim := by
  classical
  intro d ρ p hρ hp hs
  have hd : d ≠ 0 := by
    intro hz
    subst d
    have h := (hρ 0).2
    simpa [Matrix.trace] using h
  letI : NeZero d := ⟨hd⟩
  obtain ⟨v,hv,hF⟩ := simultaneous_rank_one_decomposition ρ (fun i => (hρ i).1)
  have hv' : ∀ i,ρ i=∑ a,(Matrix.vecMulVec (v i a) (star (v i a))) := hv
  have hq := vectorMass_sum v ρ hv' (fun i => (hρ i).2)
  have h := (holevo_le_blockHolevo p hp hs v ρ hv' (fun i => (hρ i).2)).trans
    (blockHolevo_le_entropy_root p hp hs v ρ hq hF)
  simpa only [entropy_owner_eq_trace_log] using h

end D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
