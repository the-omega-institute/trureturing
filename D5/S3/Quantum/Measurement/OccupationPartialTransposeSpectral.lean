/- GID: D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OccupationPartialTransposeSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal occupation operators satisfy a uniform block spectral bound. -/
/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17100
The PSD-seed model takes the source covariance reduction as input.
Occupation carriers and binomial dimensions are written as their original expressions.
The generic block positivity and real-root facts are shared with their earlier owners.
Direct frozen dependencies (declaration statement_id, not module pins):
F1: D5/S3/Quantum/Entanglement/OccupancyWordSectors.Word; statement_id=sha256:ca13ed0bb809eb9e0bcec28de917d6e1af84494bf87b4d48233eeb00ad8f61f7
F2: D5/S3/Quantum/Entanglement/OccupancyWordSectors.congr_simp; statement_id=sha256:fde6b05c0193a0ab22b642b2c553977e0270aaae7ff7a76712ab5b54f29e057d
F3: D5/S3/Quantum/Entanglement/OccupancyWordSectors.multiplicity; statement_id=sha256:7c95391e2ce98772f6771433c83507214f8702b7375e87a301f597e0d6fd7c38
F4: D5/S3/Quantum/Entanglement/OccupancyWordSectors.occupation; statement_id=sha256:7a25f213e509fae5658b7cd5566e2226a6cc4a14df4b9b97298939adea75b3ed
F5: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sectorVector; statement_id=sha256:c4dab226f71c3ad5ed5c4eb62405a22f1872b1682872934b1e1e2e37e8b62a8e
F6: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sectorWords; statement_id=sha256:7f5b56ebac6db0a78ce4980b924ba8756a829b7fa55f021a4fec28a1b7666a81
F7: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sector_gram; statement_id=sha256:2a5b5263698f977e9ae50a4d420406bbe1e6d5d9d15826bc51217f0752d5ed99
F8: D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sector_head; statement_id=sha256:ae76e3812486d02dae11ae68fdacc58f4ca9ebbae9a4b6ddcf7339046797e7b6
F9: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight; statement_id=sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
The global bound constructs the exhaustive occupation partition and dominates every block.
Partial transpose and the zero-index constructor are inlined; their I-level owners
cannot be imported by this G module.
proof_shape: occFintype: bind-only; consumer: CEntries.C_entry, CEntries.C_from_A, CEntries.mul_referenceProjector, CEntries.partialTrace_referenceProjector, Entries.compression_entry, EntryFormula.compression_entry_single, GlobalBound.global_operator_bound, RG, symmetricProjector, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_psd, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_trace, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_A_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_C_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.claim, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.result; escape_witness: none; Direct frozen dependencies: none. | proof_shape: symmetricProjector: bind-only; consumer: Entries.compression_entry, EntryFormula.A_entry, EntryFormula.A_literal_scale, EntryFormula.compression_entry_single, EntryFormula.scaled_compression_entry, RF; escape_witness: none; Direct frozen dependencies: F5. | proof_shape: occupationEmbedding: bind-only; consumer: Entries.compression_entry, Entries.embedding_snoc, EntryFormula.A_entry, EntryFormula.A_literal_scale, EntryFormula.compression_entry_single, EntryFormula.scaled_compression_entry, RF; escape_witness: none; Direct frozen dependencies: F5.
proof_shape: RF: bind-only; consumer: A, CEntries.C_from_A, EntryFormula.A_literal_scale, RG, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_A_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.claim, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.result; escape_witness: none; Direct frozen dependencies: F5. | proof_shape: outputReferenceProjector: bind-only; consumer: CEntries.C_entry, CEntries.C_from_A, CEntries.mul_referenceProjector, CEntries.partialTrace_referenceProjector, CEntries.referenceProjector_column, RG; escape_witness: none; Direct frozen dependencies: none. | proof_shape: RG: bind-only; consumer: C, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_C_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.claim, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.result; escape_witness: none; Direct frozen dependencies: F5, F9.
proof_shape: A: bind-only; consumer: BlockMatrices.A_block_entry, BlockMatrices.weighted_block, CEntries.A_reference_entry, CEntries.C_entry, CEntries.C_from_A, EntryFormula.A_entry, EntryFormula.A_literal_scale, Global.A_singleton, Global.weighted_decomposition, Global.weighted_different_blocks, Global.weighted_singleton, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_A_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: F5. | proof_shape: C: bind-only; consumer: BlockMatrices.C_block_entry, BlockMatrices.weighted_block, CEntries.C_entry, CEntries.C_from_A, Global.weighted_decomposition, Global.weighted_different_blocks, Global.weighted_singleton, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.score_C_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: F5, F9. | proof_shape: occMultiset_card: bind-only; consumer: Entries.overlap_formula; escape_witness: none; Direct frozen dependencies: none.
proof_shape: occMultiset_count: bind-only; consumer: Entries.overlap_formula, EntryFormula.occMultiset_raise; escape_witness: none; Direct frozen dependencies: none. | proof_shape: occMultiset_injective: bind-only; consumer: EntryFormula.overlap_raise; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.sum_bump: bind-only; consumer: BlockMatrices.C_block_entry, Blocks.blockIndex, Blocks.remove, Blocks.remove_blockIndex, EntryFormula.occMultiset_raise, EntryFormula.scaled_compression_entry; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Blocks.blockIndex: bind-only; consumer: BlockMatrices.A_block_entry, BlockMatrices.C_block_entry, BlockMatrices.weighted_block, Blocks.blockIndex_injective, Blocks.coupled_block_indices, Blocks.different_blocks_uncoupled, Blocks.partitionEquiv, Blocks.remove_blockIndex, EntryFormula.compression_entry_single, EntryFormula.occMultiset_raise, EntryFormula.overlap_raise, EntryFormula.scaled_compression_entry, Global.weighted_decomposition, Global.weighted_different_blocks, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_psd, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_trace; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.blockIndex_injective: bind-only; consumer: Blocks.partitionEquiv, Global.weighted_different_blocks; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.remove: bind-only; consumer: Blocks.partitionEquiv, Blocks.remove_blockIndex; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Blocks.remove_blockIndex: bind-only; consumer: Blocks.partitionEquiv; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.coupled: bind-only; consumer: BlockMatrices.A_block_entry, Blocks.coupled_block_indices, Blocks.different_blocks_uncoupled, Blocks.singleton_isolated, Global.A_singleton, Global.weighted_decomposition, Global.weighted_different_blocks; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.singleton_isolated: bind-only; consumer: Global.A_singleton, Global.weighted_decomposition; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Blocks.coupled_block_indices: bind-only; consumer: BlockMatrices.A_block_entry; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.different_blocks_uncoupled: bind-only; consumer: Global.weighted_different_blocks; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Blocks.partitionEquiv: bind-only; consumer: Global.decompositionEquiv; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Entries.occupation_snoc: bind-only; consumer: Entries.sector_snoc; escape_witness: none; Direct frozen dependencies: F1, F4. | proof_shape: Entries.sectorVector_star: bind-only; consumer: Entries.occupationVector_star; escape_witness: none; Direct frozen dependencies: F1, F3, F5, F6. | proof_shape: Entries.sector_snoc: bind-only; consumer: Entries.overlap_formula; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F8.
proof_shape: Entries.overlap: bind-only; consumer: Entries.compression_entry, Entries.overlap_formula, EntryFormula.compression_entry_single, EntryFormula.overlap_raise; escape_witness: none; Direct frozen dependencies: F1, F5. | proof_shape: Entries.overlap_formula: bind-only; consumer: EntryFormula.overlap_raise; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8. | proof_shape: Entries.embedding_snoc: bind-only; consumer: Entries.compression_entry; escape_witness: none; Direct frozen dependencies: F5, F2.
proof_shape: Entries.sum_fullword: bind-only; consumer: Entries.compression_entry; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Entries.occupationVector_star: bind-only; consumer: Entries.compression_entry; escape_witness: none; Direct frozen dependencies: F1, F3, F5, F6. | proof_shape: Entries.compression_entry: bind-only; consumer: EntryFormula.compression_entry_single; escape_witness: none; Direct frozen dependencies: F1, F3, F5, F2, F6.
proof_shape: EntryFormula.occMultiset_raise: bind-only; consumer: EntryFormula.overlap_raise; escape_witness: none; Direct frozen dependencies: none. | proof_shape: EntryFormula.overlap_raise: bind-only; consumer: EntryFormula.compression_entry_single; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8. | proof_shape: EntryFormula.compression_entry_single: bind-only; consumer: EntryFormula.scaled_compression_entry; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8.
proof_shape: EntryFormula.sqrt_scaled_product: bind-only; consumer: EntryFormula.scaled_compression_entry; escape_witness: none; Direct frozen dependencies: none. | proof_shape: EntryFormula.scaled_compression_entry: bind-only; consumer: EntryFormula.A_entry; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8. | proof_shape: EntryFormula.dimension_recursion: bind-only; consumer: EntryFormula.A_literal_scale; escape_witness: none; Direct frozen dependencies: none.
proof_shape: EntryFormula.dimension_pos: bind-only; consumer: EntryFormula.A_literal_scale, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scores, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: EntryFormula.A_literal_scale: bind-only; consumer: EntryFormula.A_entry; escape_witness: none; Direct frozen dependencies: F5. | proof_shape: EntryFormula.A_entry: bind-only; consumer: BlockMatrices.A_block_entry, CEntries.A_reference_entry, Global.A_singleton, Global.weighted_decomposition, Global.weighted_different_blocks; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8.
proof_shape: CEntries.referenceProjector_column: bind-only; consumer: CEntries.mul_referenceProjector; escape_witness: none; Direct frozen dependencies: none. | proof_shape: CEntries.mul_referenceProjector: bind-only; consumer: CEntries.partialTrace_referenceProjector; escape_witness: none; Direct frozen dependencies: none. | proof_shape: CEntries.partialTrace_referenceProjector: bind-only; consumer: CEntries.C_entry; escape_witness: none; Direct frozen dependencies: F9.
proof_shape: CEntries.C_from_A: bind-only; consumer: CEntries.C_entry; escape_witness: none; Direct frozen dependencies: F5, F9. | proof_shape: CEntries.bump_cancel: bind-only; consumer: CEntries.A_reference_entry; escape_witness: none; Direct frozen dependencies: none. | proof_shape: CEntries.A_reference_entry: bind-only; consumer: CEntries.C_entry; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8.
proof_shape: CEntries.C_entry: bind-only; consumer: BlockMatrices.C_block_entry, Global.weighted_decomposition, Global.weighted_different_blocks, Global.weighted_singleton; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9. | proof_shape: Scalar.blockMaximum: bind-only; consumer: BlockSpectral.blockOperator_bound_psd, BlockSpectral.blockOperator_rayleigh_bound, Complex.complex_rankOne_block_bound, Complex.distinguished_block_identity, GlobalBound.global_operator_bound, Scalar.blockMaximum_mono, Scalar.rankOne_block_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.blockMaximum_mono: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Scalar.topRoot: bind-only; consumer: Complex.distinguished_block_identity, GlobalBound.global_operator_bound, Scalar.rankOne_block_bound, Scalar.rankOne_plus_coordinate_bound, Scalar.topRoot_bounds, Scalar.topRoot_determinant, Scalar.topRoot_product, Scalar.topRoot_quadratic_bound, Scalar.topRoot_rankOne_identity, Scalar.topRoot_sum, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate.slope_top_eigenvalue, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate.topRoot_eq_of_certificate, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint.endpoint_from_support_family, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint.topRoot_gap_upper, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.ScalarAssembly.scalar_frontier, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.result, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.support_scaled, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_competitor_bounds, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_comparison_gap, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.real_minimizers_separated, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.residual_real_schattenPow, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.competitor_power_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.bottomRoot: bind-only; consumer: Scalar.topRoot_determinant, Scalar.topRoot_product, Scalar.topRoot_sum, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_competitor_bounds, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.real_minimizers_separated, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.residual_real_schattenPow, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.competitor_power_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.topRoot_sum: bind-only; consumer: Scalar.topRoot_determinant, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_competitor_bounds, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.residual_real_schattenPow; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Scalar.topRoot_product: bind-only; consumer: Scalar.topRoot_determinant, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.residual_real_schattenPow; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.topRoot_bounds: bind-only; consumer: GlobalBound.global_operator_bound, Scalar.topRoot_quadratic_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint.topRoot_gap_upper, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_competitor_bounds, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_comparison_gap, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.real_minimizers_separated; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.topRoot_determinant: bind-only; consumer: Scalar.topRoot_quadratic_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint.topRoot_gap_upper, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_competitor_bounds, D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.top_comparison_gap; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Scalar.quadratic_certificate: bind-only; consumer: Scalar.topRoot_quadratic_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.topRoot_quadratic_bound: bind-only; consumer: Scalar.rankOne_plus_coordinate_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.rankOne_plus_coordinate_bound: bind-only; consumer: Scalar.rankOne_block_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Scalar.topRoot_rankOne_identity: bind-only; consumer: Scalar.rankOne_block_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Scalar.rankOne_block_bound: bind-only; consumer: Complex.complex_rankOne_block_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Complex.complex_rankOne_block_bound: bind-only; consumer: BlockSpectral.blockOperator_rayleigh_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Complex.distinguished_block_identity: bind-only; consumer: GlobalBound.global_operator_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockSpectral.blockOperator: bind-only; consumer: BlockMatrices.weighted_block, BlockSpectral.blockOperator_bound_psd, BlockSpectral.blockOperator_hermitian, BlockSpectral.blockOperator_quadratic, BlockSpectral.blockOperator_rayleigh_bound, Global.weighted_decomposition, GlobalBound.gap_decomposition, GlobalBound.global_operator_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockSpectral.rankOneQuadratic: bind-only; consumer: BlockSpectral.blockOperator_quadratic, D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector; escape_witness: none; Direct frozen dependencies: none.
proof_shape: BlockSpectral.real_vector_star: bind-only; consumer: BlockSpectral.blockOperator_hermitian, BlockSpectral.blockOperator_quadratic; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockSpectral.blockOperator_hermitian: bind-only; consumer: BlockSpectral.blockOperator_bound_psd; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockSpectral.blockOperator_quadratic: bind-only; consumer: BlockSpectral.blockOperator_bound_psd, BlockSpectral.blockOperator_rayleigh_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: none.
proof_shape: BlockSpectral.blockOperator_rayleigh_bound: bind-only; consumer: BlockSpectral.blockOperator_bound_psd; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockSpectral.blockOperator_bound_psd: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockMatrices.blockVector: bind-only; consumer: BlockMatrices.A_block_entry, BlockMatrices.blockVector_norm, BlockMatrices.weighted_block, Global.weighted_decomposition, GlobalBound.gap_decomposition, GlobalBound.global_operator_bound, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.distinguished_overlap, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: none.
proof_shape: BlockMatrices.blockVector_sq: bind-only; consumer: BlockMatrices.A_block_entry, BlockMatrices.blockVector_norm, GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockMatrices.blockVector_norm: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: BlockMatrices.A_block_entry: bind-only; consumer: BlockMatrices.weighted_block; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8.
proof_shape: BlockMatrices.C_block_entry: bind-only; consumer: BlockMatrices.weighted_block; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9. | proof_shape: BlockMatrices.weighted_block: bind-only; consumer: Global.weighted_decomposition, D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9.
proof_shape: MatrixBlocks.blockDiagonal_psd: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: MatrixBlocks.fromBlocks_zero_psd: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Global.A_singleton: bind-only; consumer: Global.weighted_singleton; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8. | proof_shape: Global.weighted_singleton: bind-only; consumer: Global.weighted_decomposition; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9. | proof_shape: Global.weighted_different_blocks: bind-only; consumer: Global.weighted_decomposition; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9.
proof_shape: Global.decompositionEquiv: bind-only; consumer: Global.weighted_decomposition, GlobalBound.gap_decomposition, GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Global.weighted_decomposition: bind-only; consumer: GlobalBound.gap_decomposition; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9. | proof_shape: GlobalBound.occupation_component_le: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: GlobalBound.gap_decomposition: bind-only; consumer: GlobalBound.global_operator_bound; escape_witness: none; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9. | proof_shape: GlobalBound.global_operator_bound: content; consumer: D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores.seed_support_bound; escape_witness: GlobalBound.global_operator_bound; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F9.
-/
import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import D5.S3.Quantum.Entanglement.SequentialOccupationHistory
import D5.S3.Quantum.Information.PartialTraceMutualInformation
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
open scoped BigOperators Matrix ComplexOrder
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
noncomputable instance occFintype (N d : ℕ) : Fintype (({n : Fin d → ℕ // ∑ i, n i = N})) :=
  Fintype.ofEquiv (Sym (Fin d) N) (Sym.equivNatSumOfFintype (Fin d) N)
-- Eq. (14): sum of projectors onto the normalized vectors of Eq. (13),
-- on the actual (N+1)-qudit word carrier.
def symmetricProjector (N d : ℕ) : Matrix ((Fin (N + 1) → Fin d)) ((Fin (N + 1) → Fin d)) ℂ :=
  ∑ t : ({n : Fin d → ℕ // ∑ i, n i = (N+1)}), Matrix.vecMulVec ((sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm t).val)) (star ((sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm t).val)))
-- J sends |n;i> to the normalized N-input symmetric vector tensor |i>.
def occupationEmbedding (N d : ℕ) : Matrix ((Fin (N + 1) → Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ :=
  fun w x => (sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm x.1).val) (Fin.init w) *
    if w (Fin.last N) = x.2 then 1 else 0
-- Eq. (12), before using any occupation-basis entry lemma.
def RF (N d : ℕ) : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ :=
  (((((N+1) + d - 1).choose (d - 1)) : ℂ)⁻¹) •
    ((occupationEmbedding N d)ᴴ *
      (Matrix.of (fun (u v : Fin (N+1) → Fin d) => symmetricProjector N d
        (Fin.snoc (Fin.init v) (u (Fin.last N)))
        (Fin.snoc (Fin.init u) (v (Fin.last N))))) * occupationEmbedding N d)
def outputReferenceProjector (N d : ℕ) :
    Matrix (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)
      (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d) ℂ :=
  Matrix.kronecker (1 : Matrix ({n : Fin d → ℕ // ∑ i, n i = N})
    ({n : Fin d → ℕ // ∑ i, n i = N}) ℂ)
    (Matrix.diagonal (fun i : Fin d => if i.val = 0 then (1 : ℂ) else 0))
-- Eq. (10), with the multiplication, partial trace, and output identity literal.
def RG (N d : ℕ) : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ :=
  Matrix.kronecker (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (RF N d * outputReferenceProjector N d))
    (1 : Matrix (Fin d) (Fin d) ℂ)
def A (N d : ℕ) := ((((N + d - 1).choose (d - 1)) : ℂ) * (N + d : ℕ)) • RF N d
def C (N d : ℕ) := ((((N + d - 1).choose (d - 1)) : ℂ) * (N + d : ℕ)) • RG N d
private theorem occMultiset_card {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) : (((Sym.equivNatSumOfFintype _ _).symm n).val).card = N :=
  Sym.card_coe
private theorem occMultiset_count {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (i : Fin d) :
    (((Sym.equivNatSumOfFintype _ _).symm n).val).count i = n.val i := by
  exact congrArg (fun x : ({n : Fin d → ℕ // ∑ i, n i = N}) => x.val i)
    ((Sym.equivNatSumOfFintype (Fin d) N).apply_symm_apply n)
private theorem occMultiset_injective (N d : ℕ) : Function.Injective (fun n : ({n : Fin d → ℕ // ∑ i, n i = N}) => ((Sym.equivNatSumOfFintype (Fin d) N).symm n).val) := by
  intro n m h
  apply (Sym.equivNatSumOfFintype (Fin d) N).symm.injective
  exact Subtype.ext h
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks
open scoped BigOperators
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
private theorem sum_bump {d : ℕ} (n : Fin d → ℕ) (i : Fin d) :
    ∑ k, Function.update n i (n i + 1) k = (∑ k, n k) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) n (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega
def blockIndex {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i : Fin d) : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) :=
  (⟨Function.update m.val i (m.val i + 1), by rw [sum_bump, m.property]⟩, i)
private theorem blockIndex_injective (K d : ℕ) :
    Function.Injective (fun x : ({n : Fin d → ℕ // ∑ i, n i = K}) × Fin d => blockIndex x.1 x.2) := by
  rintro ⟨m,i⟩ ⟨m',i'⟩ h
  have hi : i = i' := congrArg Prod.snd h
  subst i'
  have hm : m = m' := by
    apply Subtype.ext
    funext k
    have hh := congrArg (fun x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) => x.1.val k) h
    simp only [blockIndex, Function.update_apply] at hh
    by_cases hki : k = i
    · subst k; simpa using hh
    · simpa [hki] using hh
  subst m'
  rfl
private def remove {K d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = (K+1)})) (i : Fin d) (hi : 0 < n.val i) : ({n : Fin d → ℕ // ∑ i, n i = K}) :=
  ⟨Function.update n.val i (n.val i - 1), by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) n.val (Finset.mem_univ i)
    rw [n.property] at hs
    omega⟩
private theorem remove_blockIndex {K d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = (K+1)})) (i : Fin d) (hi : 0 < n.val i) :
    blockIndex (remove n i hi) i = (n,i) := by
  refine Prod.ext ?_ rfl
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k; simp [blockIndex, remove, Function.update_apply]; omega
  · simp [blockIndex, remove, Function.update_apply, hki]
-- Off-diagonal coupling is possible only inside one occupation block.
private def coupled {K d : ℕ} (x y : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) : Prop :=
  Function.update y.1.val x.2 (y.1.val x.2 + 1) = Function.update x.1.val y.2 (x.1.val y.2 + 1)
private theorem singleton_isolated {K d : ℕ} (x y : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d))
    (hx : x.1.val x.2 = 0) (hxy : x ≠ y) : ¬ coupled x y := by
  intro h
  by_cases hij : x.2 = y.2
  · have hn : x.1 = y.1 := by
      apply Subtype.ext
      funext k
      have hk := congrFun h k
      simp only [coupled, Function.update_apply] at hk
      rw [hij] at hk
      by_cases hki : k = y.2
      · subst k; simpa using hk.symm
      · simpa [hki] using hk.symm
    exact hxy (Prod.ext hn hij)
  · have hi := congrFun h x.2
    simp only [coupled, Function.update_apply] at hi
    simp [hij, hx] at hi
private theorem coupled_block_indices {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i j : Fin d) :
    coupled (blockIndex m i) (blockIndex m j) := by
  by_cases hij : i = j
  · subst j; rfl
  · unfold coupled blockIndex
    simp only [Function.update_of_ne hij, Function.update_of_ne (fun h => hij h.symm)]
    exact Function.update_comm (fun h => hij h.symm) _ _ _
private theorem different_blocks_uncoupled {K d : ℕ} (m m' : ({n : Fin d → ℕ // ∑ i, n i = K})) (i j : Fin d)
    (h : m ≠ m') : ¬ coupled (blockIndex m i) (blockIndex m' j) := by
  intro hc
  apply h
  apply Subtype.ext
  funext k
  have hk := congrFun hc k
  simp only [blockIndex, Function.update_apply] at hk
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hij : i = j <;> simp_all <;> omega
-- The complete carrier is the disjoint sum of d-dimensional blocks and zero-occupation singletons.
private def partitionEquiv (K d : ℕ) :
    (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) ≃ (({n : Fin d → ℕ // ∑ i, n i = K}) × Fin d) ⊕ {x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) // x.1.val x.2 = 0} where
  toFun x := if h : x.1.val x.2 = 0 then .inr ⟨x,h⟩
    else .inl (remove x.1 x.2 (Nat.pos_of_ne_zero h),x.2)
  invFun x := match x with
    | .inl (m,i) => blockIndex m i
    | .inr x => x.val
  left_inv x := by
    by_cases hx : x.1.val x.2=0
    · simp [hx]
    · simp only [dif_neg hx]
      exact remove_blockIndex x.1 x.2 (Nat.pos_of_ne_zero hx)
  right_inv x := by
    cases x with
    | inl z =>
      rcases z with ⟨m,i⟩
      have hz : (blockIndex m i).1.val i ≠ 0 := by simp [blockIndex,Function.update_apply]
      have hz' : (blockIndex m i).1.val (blockIndex m i).2 ≠ 0 := hz
      simp only [dif_neg hz']
      congr 1
      apply (blockIndex_injective K d)
      exact remove_blockIndex (blockIndex m i).1 i (Nat.pos_of_ne_zero hz)
    | inr z =>
      simp only [z.property,dif_pos]
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Entries
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
variable {α : Type*} [Fintype α] [DecidableEq α]
private theorem occupation_snoc {N : ℕ} (u : Word α N) (i : α) :
    occupation (Fin.snoc u i) = occupation u + {i} := by
  unfold occupation
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [List.concat_eq_append, ← Multiset.coe_add]
  rfl
private theorem sectorVector_star {N : ℕ} (a : Multiset α) (u : Word α N) :
    star (sectorVector N a u) = sectorVector N a u := by
  unfold sectorVector
  split_ifs <;> simp [star_inv₀, Complex.star_def, Complex.conj_ofReal]
private theorem sector_snoc {r : Multiset α} {N : ℕ} (hr : r.card = N+1)
    (u : Word α N) (i : α) :
    sectorVector (N+1) r (Fin.snoc u i) = if i ∈ r then
      (Real.sqrt ((r.count i : ℝ)/(N+1 : ℕ)) : ℂ)*sectorVector N (r.erase i) u else 0 := by
  have ho : occupation (Fin.snoc u i) = occupation (Fin.cons i u) := by
    rw [occupation_snoc]
    have hc : occupation (Fin.cons i u) = {i} + occupation u := by
      simp only [occupation, List.ofFn_cons]
      rfl
    rw [hc, add_comm]
  have hv : sectorVector (N+1) r (Fin.snoc u i) =
      sectorVector (N+1) r (Fin.cons i u) := by
    simp [sectorVector, sectorWords, ho]
  rw [hv]
  simpa using D5.S3.Quantum.Entanglement.SequentialOccupationHistory.sector_head hr (Fin.cons i u)
-- The coefficient of a normalized (N+1)-occupation along the input occupation n and output i.
private def overlap {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (i : Fin d) (t : ({n : Fin d → ℕ // ∑ i, n i = (N+1)})) : ℂ :=
  dotProduct (star (sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm n).val)) (fun u : Fin N → Fin d => (sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm t).val) (Fin.snoc u i))
private theorem overlap_formula {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (i : Fin d) (t : ({n : Fin d → ℕ // ∑ i, n i = (N+1)})) :
    overlap n i t = if ((Sym.equivNatSumOfFintype _ _).symm n).val + {i} = ((Sym.equivNatSumOfFintype _ _).symm t).val then
      (Real.sqrt ((t.val i : ℝ)/(N+1 : ℕ)) : ℂ) else 0 := by
  have ht := occMultiset_card t
  simp only [overlap, dotProduct, Pi.star_apply, sector_snoc ht]
  by_cases hi : i ∈ ((Sym.equivNatSumOfFintype _ _).symm t).val
  · simp only [if_pos hi]
    have hsum : (∑ u : Fin N → Fin d, star (sectorVector N (((Sym.equivNatSumOfFintype _ _).symm n).val) u)*
        ((Real.sqrt (((((Sym.equivNatSumOfFintype _ _).symm t).val).count i : ℝ)/(N+1 : ℕ)) : ℂ)*
          sectorVector N ((((Sym.equivNatSumOfFintype _ _).symm t).val).erase i) u)) =
        (Real.sqrt (((((Sym.equivNatSumOfFintype _ _).symm t).val).count i : ℝ)/(N+1 : ℕ)) : ℂ)*
          (∑ u, star (sectorVector N (((Sym.equivNatSumOfFintype _ _).symm n).val) u)*sectorVector N ((((Sym.equivNatSumOfFintype _ _).symm t).val).erase i) u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hsum, sector_gram _ _ (occMultiset_card n), occMultiset_count]
    have he : ((Sym.equivNatSumOfFintype _ _).symm n).val = (((Sym.equivNatSumOfFintype _ _).symm t).val).erase i ↔ ((Sym.equivNatSumOfFintype _ _).symm n).val + {i} = ((Sym.equivNatSumOfFintype _ _).symm t).val := by
      constructor
      · intro h; exact Multiset.add_singleton_eq_iff.mpr ⟨hi,h⟩
      · intro h; exact (Multiset.add_singleton_eq_iff.mp h).2
    simp only [he, mul_ite, mul_one, mul_zero]
  · simp only [if_neg hi, mul_zero, Finset.sum_const_zero]
    have hnot : ((Sym.equivNatSumOfFintype _ _).symm n).val + {i} ≠ ((Sym.equivNatSumOfFintype _ _).symm t).val := by
      intro h
      have hm : i ∈ ((Sym.equivNatSumOfFintype _ _).symm n).val + {i} := by simp
      exact hi (h ▸ hm)
    rw [if_neg hnot]
private theorem embedding_snoc {N d : ℕ} (u : Fin N → Fin d) (a : Fin d) (x : (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) :
    occupationEmbedding N d (Fin.snoc u a) x = if a = x.2 then (sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm x.1).val) u else 0 := by
  simp [occupationEmbedding]
private theorem sum_fullword {N d : ℕ} (f : (Fin (N + 1) → Fin d) → ℂ) :
    (∑ w, f w) = ∑ a : Fin d, ∑ u : Fin N → Fin d, f (Fin.snoc u a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (N+1) => Fin d)).sum_comp f, Fintype.sum_prod_type]
  rfl
private theorem occupationVector_star {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (u : Fin N → Fin d) :
    star ((sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm n).val) u) = (sectorVector _ ((Sym.equivNatSumOfFintype _ _).symm n).val) u := sectorVector_star _ _
-- Literal compression of the partial-transposed full-word projector.
private theorem compression_entry {N d : ℕ} (n n' : ({n : Fin d → ℕ // ∑ i, n i = N})) (i j : Fin d) :
    ((occupationEmbedding N d)ᴴ * (Matrix.of (fun (u v : Fin (N+1) → Fin d) => symmetricProjector N d
        (Fin.snoc (Fin.init v) (u (Fin.last N)))
        (Fin.snoc (Fin.init u) (v (Fin.last N))))) *
      occupationEmbedding N d) (n,i) (n',j) =
      ∑ t : ({n : Fin d → ℕ // ∑ i, n i = (N+1)}), overlap n j t * overlap n' i t := by
  simp only [Matrix.mul_apply, Matrix.of_apply, sum_fullword]
  simp only [Matrix.conjTranspose_apply, embedding_snoc,
    Fin.init_snoc, Fin.snoc_last]
  simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, occupationVector_star]
  simp only [symmetricProjector, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    occupationVector_star, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [overlap, dotProduct, Pi.star_apply, occupationVector_star, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Entries
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Entries
private theorem occMultiset_raise {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (i : Fin d) :
    ((Sym.equivNatSumOfFintype _ _).symm ((blockIndex n i).1)).val = ((Sym.equivNatSumOfFintype _ _).symm n).val + {i} := by
  apply Multiset.ext.mpr
  intro k
  simp only [Multiset.count_add, occMultiset_count]
  by_cases hki : k = i <;> simp [blockIndex,Function.update_apply,Multiset.count_singleton,hki]
private theorem overlap_raise {N d : ℕ} (n : ({n : Fin d → ℕ // ∑ i, n i = N})) (i : Fin d) (t : ({n : Fin d → ℕ // ∑ i, n i = (N+1)})) :
    overlap n i t = if (blockIndex n i).1 = t then
      (Real.sqrt ((t.val i : ℝ)/(N+1 : ℕ)) : ℂ) else 0 := by
  rw [overlap_formula,← occMultiset_raise]
  simp only [(occMultiset_injective (N+1) d).eq_iff]
private theorem compression_entry_single {N d : ℕ} (n n' : ({n : Fin d → ℕ // ∑ i, n i = N})) (i j : Fin d) :
    ((occupationEmbedding N d)ᴴ * (Matrix.of (fun (u v : Fin (N+1) → Fin d) => symmetricProjector N d
        (Fin.snoc (Fin.init v) (u (Fin.last N)))
        (Fin.snoc (Fin.init u) (v (Fin.last N))))) *
      occupationEmbedding N d) (n,i) (n',j) =
      if (blockIndex n j).1 = (blockIndex n' i).1 then
        (Real.sqrt (((n.val j : ℝ)+1)/(N+1 : ℕ)) : ℂ)*
        (Real.sqrt (((n'.val i : ℝ)+1)/(N+1 : ℕ)) : ℂ) else 0 := by
  rw [compression_entry]
  simp only [overlap_raise]
  rw [Finset.sum_eq_single ((blockIndex n j).1)]
  · simp only [if_pos rfl]
    by_cases h : (blockIndex n j).1=(blockIndex n' i).1
    · have hj : ((blockIndex n j).1).val j = n.val j+1 := by simp [blockIndex,Function.update_apply]
      have hi : ((blockIndex n j).1).val i = n'.val i+1 := by rw [h]; simp [blockIndex,Function.update_apply]
      simp only [if_pos h,if_pos h.symm,hj,hi,Nat.cast_add,Nat.cast_one,if_true]
    · simp [h,Ne.symm h]
  · intro t _ ht
    simp [Ne.symm ht]
  · simp
private theorem sqrt_scaled_product (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    t*(Real.sqrt (a/t)*Real.sqrt (b/t)) = Real.sqrt (a*b) := by
  rw [Real.sqrt_div ha,Real.sqrt_div hb]
  have he : t*(Real.sqrt a/Real.sqrt t*(Real.sqrt b/Real.sqrt t)) =
      Real.sqrt a*Real.sqrt b := by
    field_simp
    rw [Real.sq_sqrt ht.le]
    ring
  rw [he,← Real.sqrt_mul ha]
private theorem scaled_compression_entry {N d : ℕ} (n n' : ({n : Fin d → ℕ // ∑ i, n i = N})) (i j : Fin d) :
    (((N+1 : ℕ) : ℂ) •
      ((occupationEmbedding N d)ᴴ * (Matrix.of (fun (u v : Fin (N+1) → Fin d) => symmetricProjector N d
        (Fin.snoc (Fin.init v) (u (Fin.last N)))
        (Fin.snoc (Fin.init u) (v (Fin.last N))))) *
        occupationEmbedding N d)) (n,i) (n',j) =
      if Function.update n'.val i (n'.val i + 1) = Function.update n.val j (n.val j + 1) then
        (Real.sqrt (((n'.val i : ℝ)+1)*((n.val j : ℝ)+1)) : ℂ) else 0 := by
  simp only [Matrix.smul_apply,smul_eq_mul,compression_entry_single]
  have hh : (blockIndex n j).1=(blockIndex n' i).1 ↔ Function.update n'.val i (n'.val i + 1)=Function.update n.val j (n.val j + 1) := by
    change (⟨Function.update n.val j (n.val j + 1),_⟩ : ({n : Fin d → ℕ // ∑ i, n i = (N+1)}))=⟨Function.update n'.val i (n'.val i + 1),_⟩ ↔ _
    simp only [Subtype.mk.injEq,eq_comm]
  simp only [hh]
  split_ifs with h
  · have he := sqrt_scaled_product ((n.val j : ℝ)+1) ((n'.val i : ℝ)+1)
      (N+1 : ℕ) (by positivity) (by positivity) (by positivity)
    have hc := congrArg (fun x : ℝ => (x : ℂ)) he
    push_cast at hc
    simpa only [Nat.cast_add,Nat.cast_one,mul_comm] using hc
  · simp
private theorem dimension_recursion {N d : ℕ} (hd : 1 ≤ d) :
    ((N + d - 1).choose (d - 1))*(N+d)=(((N+1) + d - 1).choose (d - 1))*(N+1) := by
  have h := Nat.choose_mul_succ_eq (N+d-1) (d-1)
  have h₁ : N+d-1+1=N+d := Nat.sub_add_cancel (Nat.le_add_left_of_le hd)
  have h₂ : N+d-(d-1)=N+1 := by
    simpa only [Nat.add_comm] using (Nat.add_sub_sub_cancel (b := N) hd)
  have h₃ : N+1+d-1=N+d := Nat.succ_add_sub_one d N
  simpa only [h₁,h₂,h₃] using h
theorem dimension_pos {N d : ℕ} (hd : 1 ≤ d) : 0 < ((N + d - 1).choose (d - 1)) := by
  exact Nat.choose_pos (Nat.sub_le_sub_right (Nat.le_add_left d N) 1)
private theorem A_literal_scale {N d : ℕ} (hd : 1 ≤ d) :
    A N d = ((N+1 : ℕ) : ℂ) •
      ((occupationEmbedding N d)ᴴ * (Matrix.of (fun (u v : Fin (N+1) → Fin d) => symmetricProjector N d
        (Fin.snoc (Fin.init v) (u (Fin.last N)))
        (Fin.snoc (Fin.init u) (v (Fin.last N))))) *
        occupationEmbedding N d) := by
  unfold A RF
  rw [smul_smul]
  congr 1
  have hD : ((((N+1) + d - 1).choose (d - 1)) : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos (N:=N+1) hd).ne'
  apply (mul_inv_eq_iff_eq_mul₀ hD).mpr
  have he := dimension_recursion (N:=N) hd
  exact_mod_cast (he.trans (Nat.mul_comm _ _))
private theorem A_entry {N d : ℕ} (hd : 1 ≤ d) (n n' : ({n : Fin d → ℕ // ∑ i, n i = N})) (i j : Fin d) :
    A N d (n,i) (n',j) = if Function.update n'.val i (n'.val i + 1) = Function.update n.val j (n.val j + 1) then
      (Real.sqrt (((n'.val i : ℝ)+1)*((n.val j : ℝ)+1)) : ℂ) else 0 := by
  rw [A_literal_scale hd]
  exact scaled_compression_entry n n' i j
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Entries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula
private theorem referenceProjector_column {N d : ℕ} (hd : 1 ≤ d) (x y : (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) :
    outputReferenceProjector N d x y =
      if y.2=(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d) then if x=y then 1 else 0 else 0 := by
  simp only [outputReferenceProjector, Matrix.kronecker_apply, Matrix.one_apply,
    Matrix.diagonal_apply]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    by_cases hy0 : y.2.val = 0 <;> simp_all [Matrix.one_apply,Matrix.diagonal_apply,Prod.ext_iff, Fin.ext_iff]
private theorem mul_referenceProjector {N d : ℕ} (hd : 1 ≤ d)
    (M : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ) (x y : (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) :
    (M*outputReferenceProjector N d) x y = if y.2=(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d) then M x y else 0 := by
  simp only [Matrix.mul_apply,referenceProjector_column hd]
  by_cases hy : y.2=(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)
  · simp [hy]
  · simp [hy]
private theorem partialTrace_referenceProjector {N d : ℕ} (hd : 1 ≤ d)
    (M : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ) (n m : ({n : Fin d → ℕ // ∑ i, n i = N})) :
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (M*outputReferenceProjector N d) n m =
      M (n,(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) (m,(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) := by
  simp [D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,mul_referenceProjector hd]
private theorem C_from_A {N d : ℕ} :
    C N d=Matrix.kronecker (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (A N d*outputReferenceProjector N d))
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext x y
  rcases x with ⟨n,i⟩
  rcases y with ⟨m,j⟩
  simp only [C,RG,A,Matrix.smul_apply,smul_eq_mul,Matrix.kronecker,Matrix.kronecker_apply,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,Matrix.smul_mul,Matrix.mul_apply]
  simp only [mul_assoc,← Finset.mul_sum]
private theorem bump_cancel {d : ℕ} (n m : Fin d → ℕ) (i : Fin d) :
    Function.update m i (m i + 1)=Function.update n i (n i + 1) ↔ m=n := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    simp only [Function.update_apply] at hk
    by_cases hki : k = i
    · subst k; simpa using hk
    · simpa [hki] using hk
  · rintro rfl; rfl
private theorem A_reference_entry {N d : ℕ} (hd : 1 ≤ d) (n m : ({n : Fin d → ℕ // ∑ i, n i = N})) :
    A N d (n,(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) (m,(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d))=
      if n=m then ((n.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℂ)+1) else 0 := by
  rw [A_entry hd]
  simp only [bump_cancel]
  have hm : m.val=n.val ↔ n=m := by
    constructor
    · intro h; exact (Subtype.ext h).symm
    · rintro rfl; rfl
  simp only [hm]
  split_ifs with h
  · subst m
    rw [← pow_two,Real.sqrt_sq (by positivity)]
    push_cast
    rfl
  · rfl
private theorem C_entry {N d : ℕ} (hd : 1 ≤ d) (x y : (({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) :
    C N d x y=if x=y then ((x.1.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℂ)+1) else 0 := by
  rcases x with ⟨n,i⟩
  rcases y with ⟨m,j⟩
  rw [C_from_A]
  simp only [Matrix.kronecker,Matrix.kronecker_apply,partialTrace_referenceProjector hd,A_reference_entry hd,
    Matrix.one_apply]
  by_cases hn : n=m <;> by_cases hi : i=j
  · simp [hn,hi]
  · simp [hi]
  · simp [hn]
  · simp [hn]
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
open scoped BigOperators
def blockMaximum (L p a : ℝ) : ℝ :=
  p + (1-p)*a + (p*L + (1-p) + Real.sqrt ((p*L-(1-p))^2+4*p*(1-p)*a))/2
private theorem blockMaximum_mono {L p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hab : a ≤ b) :
    blockMaximum L p a ≤ blockMaximum L p b := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hrad : (p*L-(1-p))^2+4*p*(1-p)*a ≤ (p*L-(1-p))^2+4*p*(1-p)*b := by
    nlinarith [mul_nonneg hp hq]
  have hs := Real.sqrt_le_sqrt hrad
  unfold blockMaximum
  nlinarith [mul_le_mul_of_nonneg_left hab hq]
-- The sharp largest eigenvalue formula for a real symmetric 2x2 matrix.
def topRoot (a b c : ℝ) : ℝ := (a+c+Real.sqrt ((a-c)^2+4*b^2))/2
def bottomRoot (d s t : ℝ) : ℝ := (d + t - Real.sqrt ((d - t) ^ 2 + 4 * s ^ 2)) / 2
theorem topRoot_sum (d s t : ℝ) : topRoot d s t + bottomRoot d s t = d + t := by
  unfold topRoot bottomRoot
  ring
theorem topRoot_product (d s t : ℝ) : topRoot d s t * bottomRoot d s t = d * t - s ^ 2 := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ (d - t) ^ 2 + 4 * s ^ 2 by positivity)
  unfold topRoot bottomRoot
  nlinarith
theorem topRoot_bounds (d s t : ℝ) : d ≤ topRoot d s t ∧ t ≤ topRoot d s t := by
  have hsqrt := Real.sqrt_le_sqrt (show (d - t) ^ 2 ≤ (d - t) ^ 2 + 4 * s ^ 2 by nlinarith [sq_nonneg s])
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  have habs := abs_le.mp hsqrt
  unfold topRoot
  constructor <;> linarith
theorem topRoot_determinant (d s t : ℝ) : (topRoot d s t - d) * (topRoot d s t - t) = s ^ 2 := by
  have he := topRoot_product d s t
  have hs := topRoot_sum d s t
  have hb : bottomRoot d s t = d + t - topRoot d s t := eq_sub_of_add_eq' hs
  rw [hb] at he
  nlinarith
private theorem quadratic_certificate {u v b x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : b^2 ≤ u*v) : 2*b*x*y ≤ u*x^2+v*y^2 := by
  have hs : (b*x*y)^2 ≤ (u*x^2)*(v*y^2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (mul_nonneg (sq_nonneg x) (sq_nonneg y))]
  have h := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hu (sq_nonneg x)) (mul_nonneg hv (sq_nonneg y)) hs
  nlinarith only [h]
private theorem topRoot_quadratic_bound (a b c x y : ℝ) :
    a*x^2+2*b*x*y+c*y^2 ≤ topRoot a b c*(x^2+y^2) := by
  have h := quadratic_certificate ((topRoot_bounds a b c).1 |> sub_nonneg.mpr)
    ((topRoot_bounds a b c).2 |> sub_nonneg.mpr) (topRoot_determinant a b c).symm.le
    (x := x) (y := y)
  nlinarith
private theorem rankOne_plus_coordinate_bound {ι : Type*} [Fintype ι]
    (v x : ι → ℝ) (v₀ x₀ p q : ℝ) (hp : 0 ≤ p) :
    p * (v₀*x₀ + ∑ i, v i*x i)^2 + q*x₀^2 ≤
      topRoot (p*v₀^2+q) (p*|v₀| *Real.sqrt (∑ i, (v i)^2))
        (p*∑ i, (v i)^2) * (x₀^2 + ∑ i, (x i)^2) := by
  let B : ℝ := ∑ i, (v i)^2
  let T : ℝ := ∑ i, (x i)^2
  let S : ℝ := ∑ i, v i*x i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hS : S^2 ≤ B*T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  have habsS : |S| ≤ Real.sqrt B * Real.sqrt T :=
    (Real.abs_le_sqrt hS).trans_eq (Real.sqrt_mul hB T)
  have hu : |v₀*x₀+S| ≤ |v₀| *|x₀| +Real.sqrt B*Real.sqrt T := by
    calc
      |v₀*x₀+S| ≤ |v₀*x₀| +|S| := abs_add_le _ _
      _ ≤ |v₀| *|x₀| +Real.sqrt B*Real.sqrt T := by rw [abs_mul]; linarith
  have hnonneg : 0 ≤ |v₀| *|x₀| +Real.sqrt B*Real.sqrt T := by positivity
  have hsq : (v₀*x₀+S)^2 ≤ (|v₀| *|x₀| +Real.sqrt B*Real.sqrt T)^2 := by
    nlinarith [sq_abs (v₀*x₀+S), mul_nonneg (sub_nonneg.mpr hu) (add_nonneg (abs_nonneg (v₀*x₀+S)) hnonneg)]
  have hbound := topRoot_quadratic_bound (p*v₀^2+q) (p*|v₀| *Real.sqrt B)
    (p*B) |x₀| (Real.sqrt T)
  rw [Real.sq_sqrt hT, sq_abs] at hbound
  have hexpand :
      p*(|v₀| *|x₀| +Real.sqrt B*Real.sqrt T)^2+q*x₀^2 =
        (p*v₀^2+q)*x₀^2+2*(p*|v₀| *Real.sqrt B)*|x₀| *Real.sqrt T+(p*B)*T := by
    calc
      _ = p*|v₀|^2*|x₀|^2+2*(p*|v₀| *Real.sqrt B)*|x₀| *Real.sqrt T+
          p*(Real.sqrt B)^2*(Real.sqrt T)^2+q*x₀^2 := by ring
      _ = _ := by rw [sq_abs, sq_abs, Real.sq_sqrt hB, Real.sq_sqrt hT]; ring
  change p*(v₀*x₀+S)^2+q*x₀^2 ≤ _
  calc
    p*(v₀*x₀+S)^2+q*x₀^2 ≤ p*(|v₀| *|x₀| +Real.sqrt B*Real.sqrt T)^2+q*x₀^2 :=
      by have h := mul_le_mul_of_nonneg_left hsq hp; linarith
    _ = _ := hexpand
    _ ≤ _ := hbound
private theorem topRoot_rankOne_identity (L p q a : ℝ) (ha : 0 ≤ a) (hLa : a ≤ L) :
    topRoot (p*a+q) (p*Real.sqrt a*Real.sqrt (L-a)) (p*(L-a)) =
      (p*L+q+Real.sqrt ((p*L-q)^2+4*p*q*a))/2 := by
  have hLa0 : 0 ≤ L-a := sub_nonneg.mpr hLa
  have hr : ((p*a+q)-p*(L-a))^2+4*(p*Real.sqrt a*Real.sqrt (L-a))^2 =
      (p*L-q)^2+4*p*q*a := by
    rw [mul_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hLa0]
    ring
  unfold topRoot
  rw [hr]
  ring
private theorem rankOne_block_bound {ι : Type*} [Fintype ι]
    (v x : ι → ℝ) (v₀ x₀ L a p : ℝ) (hp : 0 ≤ p)
    (ha : v₀^2=a) (hL : a+∑ i, (v i)^2=L) :
    (p+(1-p)*a)*(x₀^2+∑ i, (x i)^2) +
      p*(v₀*x₀+∑ i, v i*x i)^2+(1-p)*x₀^2 ≤
        blockMaximum L p a*(x₀^2+∑ i, (x i)^2) := by
  have hB : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have ha0 : 0 ≤ a := ha ▸ sq_nonneg v₀
  have hLa : a ≤ L := by linarith
  have hs : |v₀|=Real.sqrt a := by rw [← ha,Real.sqrt_sq_eq_abs]
  have hBval : (∑ i, (v i)^2)=L-a := (sub_eq_of_eq_add' hL.symm).symm
  have h := rankOne_plus_coordinate_bound v x v₀ x₀ p (1-p) hp
  rw [ha,hs,hBval,topRoot_rankOne_identity L p (1-p) a ha0 hLa] at h
  unfold blockMaximum
  nlinarith
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex
open scoped BigOperators
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
private theorem complex_rankOne_block_bound {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (x : ι → ℂ) (v₀ : ℝ) (x₀ : ℂ) (L a p : ℝ)
    (hp : 0 ≤ p) (ha : v₀^2=a) (hL : a+∑ i, (v i)^2=L) :
    (p+(1-p)*a)*(Complex.normSq x₀+∑ i, Complex.normSq (x i)) +
      p*Complex.normSq ((v₀:ℂ)*x₀+∑ i, (v i:ℂ)*x i)+(1-p)*Complex.normSq x₀ ≤
      blockMaximum L p a*(Complex.normSq x₀+∑ i, Complex.normSq (x i)) := by
  have hr := rankOne_block_bound v (fun i => (x i).re) v₀ x₀.re L a p hp ha hL
  have hi := rankOne_block_bound v (fun i => (x i).im) v₀ x₀.im L a p hp ha hL
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
    sub_zero,zero_add,add_zero,Complex.re_sum,Complex.im_sum,Finset.sum_add_distrib]
  simp only [pow_two] at hr hi
  linarith
-- The occupation block formula and the distinguished two-dimensional formula agree.
theorem distinguished_block_identity (n k p : ℝ) (hnk : 0 ≤ n*k) :
    blockMaximum (n+k) p n =
      topRoot (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n)) := by
  unfold blockMaximum topRoot
  have he : (p*(n+k)-(1-p))^2+4*p*(1-p)*n =
      ((n+1)-(n+p*(k+1-n)))^2+4*(p*Real.sqrt (n*k))^2 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hnk]
    ring
  rw [he]
  ring
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def blockOperator (v : ι → ℝ) (i₀ : ι) (a p : ℝ) : Matrix ι ι ℂ :=
  ((p+(1-p)*a : ℝ) : ℂ) • 1 +
  (p : ℂ) • Matrix.vecMulVec (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) +
  ((1-p : ℝ) : ℂ) • Matrix.diagonal (fun i => if i=i₀ then 1 else 0)
theorem rankOneQuadratic {n : Type*} [Fintype n] (z ψ : n → ℂ) : star z ⬝ᵥ (Matrix.vecMulVec ψ (star ψ) *ᵥ z) = (Complex.normSq (star z ⬝ᵥ ψ) : ℂ) := by
  simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [← Complex.mul_conj]
  simp only [map_sum,map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← Complex.star_def, star_star]
  ring
private theorem real_vector_star (v : ι → ℝ) :
    star (fun i => (v i : ℂ)) = (fun i => (v i : ℂ)) := by
  ext i
  simp
private theorem blockOperator_hermitian (v : ι → ℝ) (i₀ : ι) (a p : ℝ) :
    (blockOperator v i₀ a p).IsHermitian := by
  unfold blockOperator
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.add
    · exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint,Complex.star_def])
    · have h := (Matrix.posSemidef_vecMulVec_self_star (fun i => (v i : ℂ))).isHermitian
      rw [real_vector_star] at h
      exact h.smul (by simp [IsSelfAdjoint,Complex.star_def])
  · apply Matrix.IsHermitian.smul
    · apply Matrix.isHermitian_diagonal_iff.mpr
      intro i
      split_ifs <;> simp [IsSelfAdjoint]
    · simp [IsSelfAdjoint,Complex.star_def]
theorem blockOperator_quadratic (v : ι → ℝ) (i₀ : ι) (a p : ℝ) (x : ι → ℂ) :
    star x ⬝ᵥ (blockOperator v i₀ a p*ᵥx) =
      (((p+(1-p)*a)*(∑ i, Complex.normSq (x i))+
        p*Complex.normSq (∑ i, (v i:ℂ)*x i)+(1-p)*Complex.normSq (x i₀) : ℝ) : ℂ) := by
  simp only [blockOperator,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,
    dotProduct_smul,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul]
  have hnorm : star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i):ℝ):ℂ) := by
    simp only [dotProduct,Pi.star_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    exact Complex.mul_conj _
  have hrank : star x ⬝ᵥ (Matrix.vecMulVec (fun i => (v i:ℂ)) (fun i => (v i:ℂ))*ᵥx) =
      (Complex.normSq (∑ i, (v i:ℂ)*x i):ℂ) := by
    have he := rankOneQuadratic x (fun i => (v i : ℂ))
    have hc : star x ⬝ᵥ (fun i => (v i:ℂ)) = star (∑ i, (v i:ℂ)*x i) := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [real_vector_star, hc] at he
    simpa only [Complex.star_def, Complex.normSq_conj] using he
  have hcoord : star x ⬝ᵥ ((Matrix.diagonal (fun i => if i=i₀ then (1:ℂ) else 0))*ᵥx) =
      (Complex.normSq (x i₀):ℂ) := by
    simp only [dotProduct,Pi.star_apply,Matrix.mulVec_diagonal]
    simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [mul_comm]
    exact Complex.mul_conj _
  rw [hnorm,hrank,hcoord]
  push_cast
  rfl
private theorem blockOperator_rayleigh_bound {k : ℕ} (v : Fin (k+1) → ℝ)
    (x : Fin (k+1) → ℂ) (L a p : ℝ) (hp : 0 ≤ p)
    (ha : (v 0)^2=a) (hL : ∑ i, (v i)^2=L) :
    (star x ⬝ᵥ (blockOperator v 0 a p*ᵥx)).re ≤
      blockMaximum L p a*(∑ i, Complex.normSq (x i)) := by
  rw [blockOperator_quadratic,Complex.ofReal_re]
  have h := complex_rankOne_block_bound (fun i : Fin k => v i.succ)
    (fun i : Fin k => x i.succ) (v 0) (x 0) L a p hp ha
    (by rw [Fin.sum_univ_succ] at hL; rw [← ha]; exact hL)
  simpa only [Fin.sum_univ_succ] using h
private theorem blockOperator_bound_psd {k : ℕ} (v : Fin (k+1) → ℝ)
    (L a p μ : ℝ) (hp : 0 ≤ p) (ha : (v 0)^2=a)
    (hL : ∑ i, (v i)^2=L) (hμ : blockMaximum L p a ≤ μ) :
    ((μ:ℂ) • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)-blockOperator v 0 a p).PosSemidef := by
  have hh : ((μ:ℂ) • (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)-blockOperator v 0 a p).IsHermitian :=
    (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub (blockOperator_hermitian v 0 a p)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh ?_
  intro x
  have he := blockOperator_quadratic v 0 a p x
  have hb := blockOperator_rayleigh_bound v x L a p hp ha hL
  have hn : 0 ≤ ∑ i, Complex.normSq (x i) := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hbμ := mul_le_mul_of_nonneg_right hμ hn
  simp only [Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  have hnorm : star x ⬝ᵥ x=((∑ i, Complex.normSq (x i):ℝ):ℂ) := by
    simp only [dotProduct,Pi.star_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    exact Complex.mul_conj _
  rw [he,hnorm]
  simp only [smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_sub]
  rw [he,Complex.ofReal_re] at hb
  have hr : 0 ≤ μ*(∑ i, Complex.normSq (x i))-
      ((p+(1-p)*a)*(∑ i, Complex.normSq (x i))+
        p*Complex.normSq (∑ i, (v i:ℂ)*x i)+(1-p)*Complex.normSq (x 0)) := by linarith
  exact_mod_cast hr
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockMatrices
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Entries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral
def blockVector {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) : Fin d → ℝ := fun i => Real.sqrt ((m.val i:ℝ)+1)
private theorem blockVector_sq {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i : Fin d) :
    (blockVector m i)^2=(m.val i:ℝ)+1 := Real.sq_sqrt (by positivity)
private theorem blockVector_norm {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) :
    ∑ i, (blockVector m i)^2=(K:ℝ)+d := by
  simp only [blockVector_sq,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [← Nat.cast_sum,m.property]
private theorem A_block_entry {K d : ℕ} (hd : 1 ≤ d) (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i j : Fin d) :
    A (K+1) d (blockIndex m i) (blockIndex m j)=
      (if i=j then 1 else 0)+(blockVector m i:ℂ)*(blockVector m j:ℂ) := by
  rw [A_entry hd]
  have hc := coupled_block_indices m i j
  change Function.update (blockIndex m j).1.val (blockIndex m i).2 ((blockIndex m j).1.val (blockIndex m i).2 + 1)=
    Function.update (blockIndex m i).1.val (blockIndex m j).2 ((blockIndex m i).1.val (blockIndex m j).2 + 1) at hc
  rw [if_pos hc]
  by_cases hij : i=j
  · subst j
    simp only [blockIndex,Function.update_apply,if_pos rfl,if_true,Nat.cast_add,Nat.cast_one]
    rw [← pow_two,Real.sqrt_sq (by positivity)]
    have hv := congrArg (fun r : ℝ => (r:ℂ)) (blockVector_sq m i)
    push_cast at hv
    rw [← pow_two,hv]
    push_cast
    ring
  · have hji : j≠i := Ne.symm hij
    simp only [blockIndex,Function.update_apply,if_neg hij,if_neg hji,add_zero,Nat.cast_add,Nat.cast_one]
    simp only [if_neg hij,zero_add,blockVector,← Complex.ofReal_mul]
    rw [← Real.sqrt_mul (by positivity),mul_comm]
private theorem C_block_entry {K d : ℕ} (hd : 1 ≤ d) (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i j : Fin d) :
    C (K+1) d (blockIndex m i) (blockIndex m j)=
      if i=j then ((m.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℂ)+1)+(if i=(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d) then 1 else 0) else 0 := by
  rw [C_entry hd]
  have he : blockIndex m i=blockIndex m j ↔ i=j := by
    constructor
    · intro h; exact congrArg Prod.snd h
    · rintro rfl; rfl
  simp only [he]
  split_ifs with hij hi
  · subst j
    have hz : (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)=i := hi.symm
    simp [blockIndex,Function.update_apply,hz]
  · subst j
    have hz : (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)≠i := Ne.symm hi
    simp [blockIndex,Function.update_apply,hz]
  · rfl
theorem weighted_block {K d : ℕ} (hd : 1 ≤ d) (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (p : ℝ) :
    (((p:ℂ) • A (K+1) d+((1-p:ℝ):ℂ) • C (K+1) d).submatrix
      (blockIndex m) (blockIndex m)) =
      blockOperator (blockVector m) ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) ((m.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1) p := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    A_block_entry hd,C_block_entry hd,blockOperator,Matrix.one_apply,Matrix.vecMulVec_apply,
    Matrix.diagonal_apply]
  split_ifs <;> push_cast <;> ring
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockMatrices
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks
universe u v w
open scoped BigOperators Matrix ComplexOrder MatrixOrder
variable {σ : Type w} {ι : Type u} {κ : Type v} [Fintype σ] [Fintype ι] [Fintype κ]
  [DecidableEq σ] [DecidableEq ι] [DecidableEq κ]
theorem blockDiagonal_psd (B : σ → Matrix ι ι ℂ) (hB : ∀ s, (B s).PosSemidef) :
    (Matrix.blockDiagonal B).PosSemidef := by
  have h := D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal B hB
  have he : (Matrix.blockDiagonal' B).submatrix ((Equiv.sigmaEquivProd σ ι).trans (Equiv.prodComm σ ι)).symm
      ((Equiv.sigmaEquivProd σ ι).trans (Equiv.prodComm σ ι)).symm = Matrix.blockDiagonal B := by
    ext x y
    simp [Matrix.blockDiagonal, Matrix.blockDiagonal', Matrix.submatrix]
  rw [← he]
  exact h.submatrix _
private theorem fromBlocks_zero_psd (B : Matrix ι ι ℂ) (D : Matrix κ κ ℂ)
    (hB : B.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks B 0 0 D).PosSemidef := by
  letI : ∀ b : Bool, Fintype (bif b then ULift.{u} κ else ULift.{v} ι) := fun b => by cases b <;> simp only [cond_false, cond_true] <;> infer_instance
  letI : ∀ b : Bool, DecidableEq (bif b then ULift.{u} κ else ULift.{v} ι) := fun b => by cases b <;> simp only [cond_false, cond_true] <;> infer_instance
  let M : (b : Bool) → Matrix (bif b then ULift.{u} κ else ULift.{v} ι)
      (bif b then ULift.{u} κ else ULift.{v} ι) ℂ :=
    fun b => match b with
      | false => B.submatrix ULift.down ULift.down
      | true => D.submatrix ULift.down ULift.down
  have hM : ∀ b, (M b).PosSemidef := by
    intro b
    cases b
    · exact hB.submatrix ULift.down
    · exact hD.submatrix ULift.down
  let e := (Equiv.sumCongr (Equiv.ulift : ULift.{v} ι ≃ ι).symm
    (Equiv.ulift : ULift.{u} κ ≃ κ).symm).trans
      (Equiv.sumEquivSigmaBool (ULift.{v} ι) (ULift.{u} κ))
  have h := (D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal M hM).submatrix e
  have he : (Matrix.blockDiagonal' M).submatrix e e = Matrix.fromBlocks B 0 0 D := by
    ext x y
    cases x <;> cases y <;>
      simp [Matrix.submatrix, Equiv.sumEquivSigmaBool, M, e]
    all_goals apply Matrix.blockDiagonal'_apply_ne; decide
  rw [he] at h
  exact h
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Global
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockMatrices
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex
private theorem A_singleton {K d : ℕ} (hd : 1 ≤ d) (x y : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d))
    (hx : x.1.val x.2=0) : A (K+1) d x y=if x=y then 1 else 0 := by
  rcases x with ⟨n,i⟩
  rcases y with ⟨m,j⟩
  change n.val i=0 at hx
  rw [A_entry hd]
  by_cases hxy : (n,i)=(m,j)
  · cases hxy
    simp only [if_pos rfl,if_true,hx,Nat.cast_zero,zero_add,mul_one]
    norm_num
  · have h := singleton_isolated (n,i) (m,j) hx hxy
    change ¬ Function.update m.val i (m.val i + 1)=Function.update n.val j (n.val j + 1) at h
    simp [h,hxy]
private theorem weighted_singleton {K d : ℕ} (hd : 1 ≤ d) (p : ℝ)
    (x y : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) (hx : x.1.val x.2=0) :
    (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) x y=if x=y then
      ((p+(1-p)*((x.1.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1):ℝ):ℂ) else 0 := by
  simp only [AffineMap.lineMap_apply_module, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [add_comm]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,A_singleton hd x y hx,C_entry hd]
  split_ifs <;> push_cast <;> ring
private theorem weighted_different_blocks {K d : ℕ} (hd : 1 ≤ d) (p : ℝ)
    (m m' : ({n : Fin d → ℕ // ∑ i, n i = K})) (i j : Fin d) (hm : m≠m') :
    (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) (blockIndex m i) (blockIndex m' j)=0 := by
  have hc := different_blocks_uncoupled m m' i j hm
  have hxy : blockIndex m i≠blockIndex m' j := by
    intro h
    have hp : (m,i)=(m',j) := by
      apply blockIndex_injective K d
      exact h
    exact hm (congrArg Prod.fst hp)
  change ¬ Function.update (blockIndex m' j).1.val (blockIndex m i).2 ((blockIndex m' j).1.val (blockIndex m i).2 + 1)=
    Function.update (blockIndex m i).1.val (blockIndex m' j).2 ((blockIndex m i).1.val (blockIndex m' j).2 + 1) at hc
  simp only [AffineMap.lineMap_apply_module, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [add_comm]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,A_entry hd,
    if_neg hc,C_entry hd,if_neg hxy,mul_zero,add_zero]
private def decompositionEquiv (K d : ℕ) :
    (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) ≃ (Fin d × ({n : Fin d → ℕ // ∑ i, n i = K})) ⊕ {x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) // x.1.val x.2 = 0} :=
  (partitionEquiv K d).trans ((Equiv.prodComm (({n : Fin d → ℕ // ∑ i, n i = K})) (Fin d)).sumCongr (Equiv.refl _))
-- This equation is the whole-space matrix decomposition, including singletons.
private theorem weighted_decomposition {K d : ℕ} (hd : 1 ≤ d) (p : ℝ) :
    ((AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ))).submatrix (decompositionEquiv K d).symm (decompositionEquiv K d).symm =
    Matrix.fromBlocks
      (Matrix.blockDiagonal (fun m : ({n : Fin d → ℕ // ∑ i, n i = K}) =>
        blockOperator (blockVector m) ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) ((m.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1) p))
      0 0
      (Matrix.diagonal (fun x : {x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) // x.1.val x.2 = 0} =>
        ((p+(1-p)*((x.val.1.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1):ℝ):ℂ))) := by
  ext x y
  cases x with
  | inl x =>
    rcases x with ⟨i,m⟩
    cases y with
    | inl y =>
      rcases y with ⟨j,m'⟩
      change (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) (blockIndex m i) (blockIndex m' j)=
        if m=m' then blockOperator (blockVector m) ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) ((m.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1) p i j else 0
      by_cases hm : m=m'
      · subst m'
        rw [if_pos rfl]
        simpa only [AffineMap.lineMap_apply_module, Complex.ofReal_sub, Complex.ofReal_one, Matrix.submatrix_apply, add_comm] using
          congrArg (fun B : Matrix (Fin d) (Fin d) ℂ => B i j) (weighted_block hd m p)
      · rw [if_neg hm]
        exact weighted_different_blocks hd p m m' i j hm
    | inr y =>
      change (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) (blockIndex m i) y.val=0
      have hxy : blockIndex m i≠y.val := by
        intro h
        have hpos : 0 < (blockIndex m i).1.val (blockIndex m i).2 := by simp [blockIndex,Function.update_apply]
        have hz : (blockIndex m i).1.val (blockIndex m i).2=0 := by rw [h]; exact y.property
        exact (Nat.ne_of_gt hpos) hz
      have hc : ¬ coupled (blockIndex m i) y.val := by
        intro h
        exact singleton_isolated y.val (blockIndex m i) y.property (Ne.symm hxy) h.symm
      rcases y with ⟨⟨n,j⟩,hy⟩
      change ¬ Function.update n.val (blockIndex m i).2 (n.val (blockIndex m i).2 + 1)=Function.update (blockIndex m i).1.val j ((blockIndex m i).1.val j + 1) at hc
      simp only [AffineMap.lineMap_apply_module, ← Complex.ofReal_one, ← Complex.ofReal_sub]
      rw [add_comm]
      simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,A_entry hd,
        if_neg hc,C_entry hd,if_neg hxy,mul_zero,add_zero]
  | inr x =>
    cases y with
    | inl y =>
      rcases y with ⟨j,m⟩
      change (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) x.val (blockIndex m j)=0
      have hxy : x.val≠blockIndex m j := by
        intro h
        have hh := congrArg (fun x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) => x.1.val x.2) h
        rw [x.property] at hh
        simp [blockIndex,Function.update_apply] at hh
      rw [weighted_singleton hd p x.val (blockIndex m j) x.property,if_neg hxy]
    | inr y =>
      change (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ)) x.val y.val = if x=y then _ else 0
      rw [weighted_singleton hd p x.val y.val x.property]
      simp only [Subtype.val_inj]
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Global
namespace D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.GlobalBound
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockMatrices
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.MatrixBlocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Global
private theorem occupation_component_le {K d : ℕ} (m : ({n : Fin d → ℕ // ∑ i, n i = K})) (i : Fin d) : m.val i ≤ K := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (m.val j))
    (Finset.mem_univ i)
  rwa [m.property] at h
private theorem gap_decomposition {K d : ℕ} (hd : 1 ≤ d) (p μ : ℝ) :
    (((μ:ℂ) • (1 : Matrix ((({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) ℂ)-
      (AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ))).submatrix (decompositionEquiv K d).symm (decompositionEquiv K d).symm) =
    Matrix.fromBlocks
      (Matrix.blockDiagonal (fun m : ({n : Fin d → ℕ // ∑ i, n i = K}) =>
        (μ:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)-
        blockOperator (blockVector m) ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)) ((m.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1) p))
      0 0
      (Matrix.diagonal (fun x : {x : (({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d) // x.1.val x.2 = 0} =>
        ((μ-(p+(1-p)*((x.val.1.val ((⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ : Fin d)):ℝ)+1)):ℝ):ℂ))) := by
  rw [Matrix.submatrix_sub,Matrix.submatrix_smul]
  change ((μ:ℂ) • (1 : Matrix ((({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = (K+1)}) × Fin d)) ℂ).submatrix
    (decompositionEquiv K d).symm (decompositionEquiv K d).symm -
    ((AffineMap.lineMap (C (K+1) d) (A (K+1) d) (p : ℂ))).submatrix (decompositionEquiv K d).symm (decompositionEquiv K d).symm) = _
  rw [Matrix.submatrix_one_equiv,weighted_decomposition hd]
  ext x y
  cases x <;> cases y <;>
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Matrix.blockDiagonal_apply,Matrix.diagonal_apply,Sum.inr.injEq,Sum.inl.injEq]
  · rename_i x y
    rcases x with ⟨i,m⟩
    rcases y with ⟨j,m'⟩
    by_cases hm : m=m' <;> by_cases hi : i=j <;> simp [hm,hi]
  · simp
  · simp
  · rename_i x y
    split_ifs <;> push_cast <;> ring
theorem global_operator_bound {K k : ℕ} (hk : 1 ≤ k) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ((blockMaximum ((K:ℝ)+k+1) p ((K:ℝ)+1):ℂ) •
      (1 : Matrix ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ℂ)-
      (AffineMap.lineMap (C (K+1) (k+1)) (A (K+1) (k+1)) (p : ℂ))).PosSemidef := by
  have hd : 1 ≤ k+1 := Nat.le_add_right_of_le hk
  let μ := blockMaximum ((K:ℝ)+k+1) p ((K:ℝ)+1)
  apply (Matrix.posSemidef_submatrix_equiv (decompositionEquiv K (k+1)).symm).mp
  rw [gap_decomposition hd p μ]
  apply fromBlocks_zero_psd
  · apply blockDiagonal_psd
    intro m
    have ha : (blockVector m 0)^2=((m.val ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1))):ℝ)+1) := by
      rw [blockVector_sq]
      rfl
    have hnorm : ∑ i, (blockVector m i)^2=(K:ℝ)+k+1 := by
      rw [blockVector_norm]
      push_cast
      ring
    apply blockOperator_bound_psd (blockVector m) ((K:ℝ)+k+1)
      ((m.val ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1))):ℝ)+1) p μ hp ha hnorm
    apply blockMaximum_mono hp hp1
    have hc := occupation_component_le m ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1)))
    exact_mod_cast (Nat.add_le_add_right hc 1)
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro x
    have hn := occupation_component_le x.val.1 ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1)))
    have hnreal : (x.val.1.val ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1))):ℝ)+1 ≤ (K:ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
    have hm : p+(1-p)*((x.val.1.val ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k+1))):ℝ)+1) ≤ (K:ℝ)+2 := by
      nlinarith [mul_nonneg hp (show 0 ≤ (K:ℝ)+1 by positivity)]
    have hμ : (K:ℝ)+2 ≤ μ := by
      dsimp [μ]
      rw [show (K:ℝ)+k+1=((K:ℝ)+1)+k by ring,distinguished_block_identity ((K:ℝ)+1) k p (by positivity)]
      rw [show (K:ℝ)+2=(K:ℝ)+1+1 by ring]
      exact (topRoot_bounds _ _ _).1
    exact_mod_cast sub_nonneg.mpr (hm.trans hμ)
end D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.GlobalBound
end
