/- GID: D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two-positive maps obey the transition trace estimate. -/

/- Judgement:
   admission_basis: escape-witness.
   Module escape_witness: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one.
   Direct frozen dependencies:
   D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.KPositive: statement_id sha256:cfcd166642f631cc07b186e808f4d33b69142d6b8102039bb244de31a01401c9.
   D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef: statement_id sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3.
   Information-escape registration is paused under CLAUDE.md §3.9.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_apply: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.pair_extraction, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_single_star, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_add, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_smul, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.traceIdentity_twoPositive, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_positive, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.positive_diag_of_two, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_block, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplify_star, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_congruence, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_comp, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.minReSpectrum: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.spectralBound, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.SourceTheorem1Bound, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.minReSpectrum_attained, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_hsAdjoint, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_conj, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.SimilarityCertificate, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_affine, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_smul, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.maxReSpectrum: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.spectralBound, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_hsAdjoint, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_conj, D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.PerronCertificate, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_affine, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_smul, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.spectralBound: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_rescaling_is_algebraic, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_route_conditional, D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.claim, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.differenceQuotient_bound, D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.result.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.psiPlus: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.block_plus, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.pair_extraction, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_single_star, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.psiMinus: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.pair_extraction.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.block_plus: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.pair_extraction, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_single_star, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.pair_extraction: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.trace_standard: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_trace_bound, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_trace_bound: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_single_star: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_star_preserving.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_star_preserving: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_add: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_smul: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_strict, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.traceIdentity_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real, D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_positive: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_strictly_improving, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed, _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real, D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.regularization_strictly_improving: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_strict, _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.regularized_perron_and_max_real.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.positive_diag_of_two: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_colStochastic, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_colStochastic: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsInner: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.weightedAdjoint, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_inner_left, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_entry, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_star, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_congr, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_comp, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_tracePreserving, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_toMatrix, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_charpoly, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_trace, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_roots, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.realParts_hsAdjoint, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_hsAdjoint, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_supertrace, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.weightedAdjoint: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_tracePreserving, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_supertrace, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_inner_left: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_entry, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_congr, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_tracePreserving.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.trace_rank_one: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.psd_of_trace_pairing.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.psd_of_trace_pairing: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.trace_mul_psd_nonneg: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_entry: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_star, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_toMatrix.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_block: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsPair_blocks: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsPair_left_ext: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsAdjoint_star: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplify_star: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_congruence: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.congrMap_twoPositive.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.congrMap_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.twoPositive_comp: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superoperator_trace_real_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.differenceQuotient_trace_real.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.positive_map_norm_four: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.positive_power_fixed: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one: proof_shape: content; escape_witness: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.faithful_fixed_eigenvalue_norm_le_one; consumer: _private.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.0.D5.S3.Quantum.QuantumChannels.FaithfulPerronRegularization.faithful_perron_eigenvalue_bound.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.root_mem_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.roots_nonempty, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.roots_finite: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.minReSpectrum_attained, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_affine.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.roots_nonempty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.minReSpectrum_attained, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.extrema_affine.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_close_of_roots_close: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.polynomial_extrema_close.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.polynomial_extrema_close: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.polyRootMin: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.polyRootMax: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.charpoly_coeff_continuous: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.charpoly_end_coeff_continuous.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.charpoly_end_coeff_continuous: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.root_norm_le_operator_norm: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.positive_root_modulus: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.extrema_tendsto: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound, D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.result.
   D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.superTrace_continuous: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound, D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.result.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_re_stochastic_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.transition_colStochastic.
   _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.matrix_inner_trace: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsPair_blocks, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.hsPair_left_ext, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.amplification_adjoint_pair, _private.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.0.D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.adjoint_twoPositive_of_star, D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.unital_iff_adjoint_tracePreserving.
-/
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import D5.S3.Weil.ZetaLinear.RankTrace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal NNReal
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
namespace D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
variable {d : ℕ}
private theorem amplification_apply {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ) (a b : Fin 2 × Fin d) :
    MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ X a b =
      Φ (fun i j => X (a.1,i) (b.1,j)) a.2 b.2:= by
 classical
 rw [MatrixMap.kron_def]
 change (∑ x : Fin 2, ∑ y : Fin 2, ∑ i : Fin d, ∑ j : Fin d,
   (if x = a.1 ∧ y = b.1 then (1 : ℂ) else 0) *
    Φ (Matrix.single i j 1) a.2 b.2 * X (x,i) (y,j)) = _
 simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
 simp only [ite_and]
 simp
 have hx : (fun i j => X (a.1,i) (b.1,j)) =
     ∑ i : Fin d, ∑ j : Fin d, X (a.1,i) (b.1,j) • Matrix.single i j (1 : ℂ) := by
   ext i j
   simp [Matrix.single,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,ite_and]
 rw [hx]
 simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
 apply Finset.sum_congr rfl
 intro i hi
 apply Finset.sum_congr rfl
 intro j hj
 exact mul_comm _ _
section
variable {d : ℕ}
def minReSpectrum {d : ℕ} (L : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : ℝ :=
  sInf ((fun z : ℂ => z.re) '' {z : ℂ | z ∈ (L.charpoly.roots)})
def maxReSpectrum {d : ℕ} (L : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : ℝ :=
  sSup ((fun z : ℂ => z.re) '' {z : ℂ | z ∈ (L.charpoly.roots)})
def spectralBound {d : ℕ} (L : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) L)).re ≤
    (d : ℝ) * minReSpectrum L + ((d : ℝ)^2 - d) * maxReSpectrum L
end
section
variable {d : ℕ}
private def psiPlus {d : ℕ} (j k : Fin d) : Fin 2 × Fin d → ℂ :=
  fun a => if a.1 = 0 then (Pi.single k (1 : ℂ) : Fin d → ℂ) a.2
    else (Pi.single j (1 : ℂ) : Fin d → ℂ) a.2
private def psiMinus {d : ℕ} (j k : Fin d) : Fin 2 × Fin d → ℂ :=
  fun a => if a.1 = 0 then (Pi.single k (1 : ℂ) : Fin d → ℂ) a.2
    else -((Pi.single j (1 : ℂ) : Fin d → ℂ) a.2)
private lemma block_plus {d : ℕ} (j k : Fin d) (a b : Fin 2) :
    (fun i l => (Matrix.vecMulVec (psiPlus j k) (star (psiPlus j k))) (a,i) (b,l)) =
      Matrix.single (if a = 0 then k else j) (if b = 0 then k else j) 1 := by
  ext i l
  simp [Matrix.vecMulVec_apply, psiPlus, Pi.single_apply, eq_comm, Matrix.single]
  split_ifs <;> simp_all <;> grind
lemma pair_extraction {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Φ)) (j k : Fin d) :
    (Φ (Matrix.single k j 1) k j).re + (Φ (Matrix.single j k 1) j k).re ≤
      (Φ (Matrix.single k k 1) k k).re + (Φ (Matrix.single j j 1) j j).re := by
  let X := Matrix.vecMulVec (psiPlus j k) (star (psiPlus j k))
  have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hA := h2 hX
  have hq := hA.dotProduct_mulVec_nonneg (psiMinus j k)
  have hqr := hq.1
  simp only [X, amplification_apply, block_plus] at hqr
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
    psiMinus, Pi.single_apply, eq_comm, Complex.add_re, Complex.sub_re,
    Complex.neg_re] at hqr
  simp [amplification_apply, block_plus] at hqr
  linarith
private theorem trace_standard {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Φ =
      ∑ i : Fin d, ∑ j : Fin d, Φ (Matrix.single i j 1) i j := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single,
    Fintype.sum_prod_type, Matrix.stdBasis, ← Matrix.single_eq_of_single_single]
theorem transition_trace_bound {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Φ)) :
    (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Φ).re ≤
      (d : ℝ) * ∑ i : Fin d, (Φ (Matrix.single i i 1) i i).re := by
  let a : Fin d → Fin d → ℝ := fun i j => (Φ (Matrix.single i j 1) i j).re
  let b : Fin d → ℝ := fun i => a i i
  have hpairs : (∑ i : Fin d, ∑ j : Fin d, (a i j + a j i)) ≤
      ∑ i : Fin d, ∑ j : Fin d, (b i + b j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact pair_extraction Φ h2 j i
  have hsum : (∑ i : Fin d, ∑ j : Fin d, a j i) =
      ∑ i : Fin d, ∑ j : Fin d, a i j := Finset.sum_comm
  simp only [Finset.sum_add_distrib] at hpairs
  rw [hsum] at hpairs
  have hdiag : (∑ i : Fin d, ∑ j : Fin d, (b i + b j)) =
      2 * (d : ℝ) * ∑ i : Fin d, b i := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  simp only [Finset.sum_add_distrib] at hdiag
  rw [hdiag] at hpairs
  rw [trace_standard]
  simp only [Complex.re_sum]
  change (∑ i : Fin d, ∑ j : Fin d, a i j) ≤ (d : ℝ) * ∑ i : Fin d, b i
  linarith
end
section
variable {d : ℕ}
private lemma twoPositive_single_star {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Φ))
    (j k : Fin d) :
    (Φ (Matrix.single k j 1)).conjTranspose = Φ (Matrix.single j k 1) := by
  have h := (h2 (Matrix.posSemidef_vecMulVec_self_star (psiPlus j k))).isHermitian
  ext a b
  have hab := h.apply (1,a) (0,b)
  simpa [amplification_apply, block_plus] using hab
lemma twoPositive_star_preserving {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Φ))
    (Y : (Matrix (Fin d) (Fin d) ℂ)) : Φ Y.conjTranspose = (Φ Y).conjTranspose := by
  have hexpand (X : (Matrix (Fin d) (Fin d) ℂ)) : X = ∑ i : Fin d, ∑ j : Fin d, X i j • Matrix.single i j 1 := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  rw [hexpand Y]
  have hYstar :
      (∑ x : Fin d, ∑ y : Fin d, Y x y • Matrix.single x y (1 : ℂ)).conjTranspose =
        ∑ x : Fin d, ∑ y : Fin d, star (Y x y) • Matrix.single y x (1 : ℂ) := by
    rw [Matrix.conjTranspose_sum (Finset.univ)]
    simp_rw [Matrix.conjTranspose_sum (Finset.univ), Matrix.conjTranspose_smul,
      Matrix.conjTranspose_single]
    simp
  rw [hYstar]
  ext i j
  simp only [map_sum, map_smul]
  rw [Matrix.conjTranspose_sum (Finset.univ)]
  simp_rw [Matrix.conjTranspose_sum (Finset.univ), Matrix.conjTranspose_smul]
  have hmat (x y : Fin d) :
      Φ (Matrix.single y x 1) = (Φ (Matrix.single x y 1)).conjTranspose := by
    exact (twoPositive_single_star Φ h2 y x).symm
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => M i j)
    (congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => star (Y x y) • M) (hmat x y))
end
section
variable {d : ℕ}
lemma twoPositive_add {d : ℕ} (Φ Ψ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hΦ : (KPositive 2 _ Φ)) (hΨ : (KPositive 2 _ Ψ)) : (KPositive 2 _ (Φ + Ψ)) := by
  intro X hX
  have h : (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) (Φ + Ψ)) X = (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ) X + (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Ψ) X := by
    ext a b
    simp only [amplification_apply, LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [h]
  exact (hΦ hX).add (hΨ hX)
lemma twoPositive_smul {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hΦ : (KPositive 2 _ Φ))
    (c : ℝ) (hc : 0 ≤ c) : (KPositive 2 _ ((c : ℂ) • Φ)) := by
  intro X hX
  have h : (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((c : ℂ) • Φ)) X = (c : ℂ) • (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ) X := by
    ext a b
    simp only [amplification_apply, LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [h]
  change (c • (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ) X).PosSemidef
  exact (hΦ hX).smul hc
lemma traceIdentity_twoPositive {d : ℕ} : (KPositive 2 _ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ)))) := by
  intro X hX
  let Y : Matrix (Fin 2) (Fin 2) ℂ :=
    ∑ k : Fin d, X.submatrix (fun a => (a,k)) (fun b => (b,k))
  have hY : Y.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro k _
    exact hX.submatrix (fun a => (a,k))
  have hYI := hY.kronecker (Matrix.PosSemidef.one (n := Fin d) (R := ℂ))
  have h : (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) (((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ)))) X = Matrix.kronecker Y (1 : (Matrix (Fin d) (Fin d) ℂ)) := by
    ext a b
    simp [amplification_apply, LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.trace, Y, Matrix.kronecker_apply,
      Finset.sum_mul, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [h]
  exact hYI
lemma regularization_twoPositive {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hT : (KPositive 2 _ T)) (ε : ℝ) (hε : 0 ≤ ε) :
    (KPositive 2 _ (T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ)))) :=
  twoPositive_add _ _ hT (twoPositive_smul _ traceIdentity_twoPositive ε hε)
lemma twoPositive_positive {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hT : (KPositive 2 _ T))
    (X : (Matrix (Fin d) (Fin d) ℂ)) (hX : X.PosSemidef) : (T X).PosSemidef := by
  have h := hT (x := X.submatrix (Prod.snd : Fin 2 × Fin d → Fin d) Prod.snd) (hX.submatrix Prod.snd)
  have hsub := h.submatrix (fun i : Fin d => ((0 : Fin 2),i))
  have he : ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) T)
      (X.submatrix Prod.snd Prod.snd)).submatrix
        (fun i : Fin d => ((0 : Fin 2), i)) (fun i : Fin d => ((0 : Fin 2), i)) = T X := by
    ext i j
    simp only [Matrix.submatrix_apply, amplification_apply]
  rw [he] at hsub
  exact hsub
lemma regularization_strictly_improving {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hT : (KPositive 2 _ T)) (ε : ℝ) (hε : 0 < ε)
    (X : (Matrix (Fin d) (Fin d) ℂ)) (hX : X.PosSemidef) (hne : X ≠ 0) :
    (((T + (ε : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) X).PosDef := by
  have htrreal : ((Matrix.trace X).re : ℂ) = Matrix.trace X := by
    apply Complex.ext
    · rfl
    · simpa using hX.trace_nonneg.2
  have htrne : (Matrix.trace X).re ≠ 0 := by
    intro hz
    have hz' : Matrix.trace X = 0 := by rw [← htrreal, hz]; simp
    exact hne (hX.trace_eq_zero_iff.mp hz')
  have htrpos : 0 < (Matrix.trace X).re :=
    lt_of_le_of_ne hX.trace_nonneg.1 (Ne.symm htrne)
  change (T X + (ε : ℂ) • (Matrix.trace X • (1 : (Matrix (Fin d) (Fin d) ℂ)))).PosDef
  rw [← htrreal, smul_smul, ← Complex.ofReal_mul]
  change (T X + (ε * (Matrix.trace X).re : ℝ) • (1 : (Matrix (Fin d) (Fin d) ℂ))).PosDef
  exact Matrix.PosDef.posSemidef_add (twoPositive_positive T hT X hX)
    (Matrix.PosDef.one.smul (mul_pos hε htrpos))
end
section
variable {d : ℕ}
lemma positive_diag_of_two {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Φ))
    (i j : Fin d) : 0 ≤ (Φ (Matrix.single j j 1) i i).re := by
  let v : Fin 2 × Fin d → ℂ := Pi.single (0,j) 1
  let X := Matrix.vecMulVec v (star v)
  have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hA := h2 hX
  have hdiag := hA.diag_nonneg (i := (0,i))
  have hself : IsSelfAdjoint (((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ) X) (0,i) (0,i)) :=
    hA.isHermitian.apply (0,i) (0,i)
  have hre := (Complex.re_nonneg_iff_nonneg hself).mpr hdiag
  rw [Matrix.single_eq_of_single_single j j 1]
  have hmat : Matrix.of (Pi.single j (Pi.single j 1)) =
      (fun a b => X (0,a) (0,b)) := by
    ext a b
    simp [X, v, Matrix.vecMulVec_apply, Pi.single_apply]
    by_cases ha : a = j <;> by_cases hb : b = j <;> simp [ha, hb]
  rw [hmat]
  simpa only [amplification_apply] using hre
end
section
variable {d : ℕ}
def transition (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Φ (Matrix.single j j 1) i i
private lemma transition_re_stochastic_iff
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    (transition Φ).map Complex.re ∈ Matrix.colStochastic ℝ (Fin d) ↔
      (∀ i j, 0 ≤ (Φ (Matrix.single j j 1) i i).re) ∧
        (∀ j, ∑ i, (Φ (Matrix.single j j 1) i i).re = 1) := by
  rw [Matrix.mem_colStochastic_iff_sum]
  rfl
theorem transition_colStochastic {d : ℕ} [NeZero d]
    (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hpos : ∀ i j : Fin d, 0 ≤ (Φ (Matrix.single j j 1) i i).re)
    (htp : (∀ X, Matrix.trace (Φ X) = Matrix.trace X)) :
    (transition Φ).map Complex.re ∈ Matrix.colStochastic ℝ (Fin d) := by
  apply (transition_re_stochastic_iff Φ).2
  constructor
  · intro i j
    exact hpos i j
  · intro j
    have hj := congrArg Complex.re (htp (Matrix.single j j 1))
    simp [transition, Matrix.trace] at hj ⊢
    simpa [Matrix.trace, transition] using hj
end
section
variable {d : ℕ}
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace
@[instance_reducible]
noncomputable def hsInner : @InnerProductSpace ℂ ((Matrix (Fin d) (Fin d) ℂ)) _ (Matrix.frobeniusSeminormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) :=
  { toNormedSpace := Matrix.frobeniusNormedSpace
    inner := fun X Y => (X.conjTranspose * Y).trace
    norm_sq_eq_re_inner := by
      intro X
      rw [Matrix.trace_mul_comm X.conjTranspose X]
      rw [Matrix.frobenius_norm_def]
      have hrpow :
          ((∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
            ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) := by
        rw [← Real.rpow_mul
          (by positivity : 0 ≤ (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ)))]
        norm_num
      calc
        ((∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
            ∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ) := by
          convert hrpow using 1 <;> norm_num
        _ = RCLike.re (X * X.conjTranspose).trace := by
          norm_num [Real.rpow_natCast, Complex.sq_norm, Complex.normSq_apply,
            Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    conj_inner_symm := by
      intro X Y
      have h := (Matrix.toMatrixInnerProductSpace (1 : Matrix (Fin d) (Fin d) ℂ)
        Matrix.PosSemidef.one).conj_inner_symm X Y
      change star ((X * 1 * Y.conjTranspose).trace) = (Y * 1 * X.conjTranspose).trace at h
      simp only [Matrix.mul_one] at h
      rw [Matrix.trace_mul_comm X Y.conjTranspose, Matrix.trace_mul_comm Y X.conjTranspose] at h
      exact h
    add_left := by
      intro X Y Z
      have h := (Matrix.toMatrixInnerProductSpace (1 : Matrix (Fin d) (Fin d) ℂ)
        Matrix.PosSemidef.one).add_left X Y Z
      change (Z * 1 * (X + Y).conjTranspose).trace =
        (Z * 1 * X.conjTranspose).trace + (Z * 1 * Y.conjTranspose).trace at h
      simp only [Matrix.mul_one] at h
      rw [Matrix.trace_mul_comm Z (X + Y).conjTranspose,
        Matrix.trace_mul_comm Z X.conjTranspose, Matrix.trace_mul_comm Z Y.conjTranspose] at h
      exact h
    smul_left := by
      intro X Y r
      have h := (Matrix.toMatrixInnerProductSpace (1 : Matrix (Fin d) (Fin d) ℂ)
        Matrix.PosSemidef.one).smul_left X Y r
      change (Y * 1 * (r • X).conjTranspose).trace = star r * (Y * 1 * X.conjTranspose).trace at h
      simp only [Matrix.mul_one] at h
      rw [Matrix.trace_mul_comm Y (r • X).conjTranspose, Matrix.trace_mul_comm Y X.conjTranspose] at h
      exact h
    }
attribute [local instance 2000] hsInner
def weightedAdjoint (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (W V : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  ((LinearMap.mulLeftRight ℂ (W, W.conjTranspose))).comp (((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi).comp ((LinearMap.mulLeftRight ℂ (V, V.conjTranspose))))
lemma hsAdjoint_inner_left (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (X Y : (Matrix (Fin d) (Fin d) ℂ)) :
    inner ℂ ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y) X = inner ℂ Y (Phi X) := by
  let hfd : @Module.Finite ℂ ((Matrix (Fin d) (Fin d) ℂ)) _ _
      (@NormedSpace.toModule ℂ ((Matrix (Fin d) (Fin d) ℂ)) _ (Matrix.frobeniusSeminormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) Matrix.frobeniusNormedSpace) := by
    exact FiniteDimensional.finiteDimensional_pi' ℂ _
  exact @LinearMap.adjoint_inner_left ℂ ((Matrix (Fin d) (Fin d) ℂ)) ((Matrix (Fin d) (Fin d) ℂ)) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner hfd hfd Phi X Y
end
section
variable {d : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma trace_rank_one (X : Matrix n n ℂ) (v : n → ℂ) :
    (X * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ (X *ᵥ v) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
private lemma psd_of_trace_pairing (X : Matrix n n ℂ) (hX : X.IsHermitian)
    (hp : ∀ Y : Matrix n n ℂ, Y.PosSemidef → 0 ≤ (X * Y).trace.re) :
    X.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hX
  intro v
  have hn := hp (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
  rw [trace_rank_one] at hn
  exact Complex.nonneg_iff.mpr ⟨hn, (hX.im_star_dotProduct_mulVec_self v).symm⟩
end
section
variable {d : ℕ}
private lemma trace_mul_psd_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace.re := by
  exact RHLinalg.trace_mul_nonneg_of_posSemidef hX hY
end
section
variable {d : ℕ}
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
lemma hsAdjoint_entry (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (Y : (Matrix (Fin d) (Fin d) ℂ)) (a b : Fin d) :
    (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y a b =
      ∑ i : Fin d, ∑ j : Fin d, star (Phi (Matrix.single a b 1) i j) * Y i j := by
  have hinner (X Y : (Matrix (Fin d) (Fin d) ℂ)) : inner ℂ X Y = (Y * X.conjTranspose).trace := by
    exact Matrix.trace_mul_comm X.conjTranspose Y
  have h := hsAdjoint_inner_left Phi (Matrix.single a b 1) Y
  rw [hinner, hinner] at h
  change (Matrix.single a b 1 * ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y).conjTranspose).trace =
    (Phi (Matrix.single a b 1) * Y.conjTranspose).trace at h
  rw [Matrix.trace_single_mul] at h
  have hs := congrArg star h
  simp only [one_smul, Matrix.conjTranspose_apply, star_star] at hs
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] at hs
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm] using hs
end
section
variable {d : ℕ}
private lemma matrix_inner_trace {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    (Matrix.toMatrixInnerProductSpace (1 : Matrix n n ℂ) Matrix.PosSemidef.one).inner X Y =
      (Y * X.conjTranspose).trace := by
  change (Y * 1 * X.conjTranspose).trace = _
  rw [Matrix.mul_one]
private theorem amplification_block
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ) (a b : Fin 2) :
    Matrix.submatrix (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Φ X) (Prod.mk a) (Prod.mk b) = Φ (Matrix.submatrix X (Prod.mk a) (Prod.mk b)) := by
  ext i j
  exact amplification_apply Φ X (a,i) (b,j)
private lemma hsPair_blocks {d : ℕ} (X Y : (Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ)) :
    (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner X Y = ∑ a : Fin 2, ∑ b : Fin 2, (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner (Matrix.submatrix X (Prod.mk a) (Prod.mk b)) (Matrix.submatrix Y (Prod.mk a) (Prod.mk b)) := by
  simp only [matrix_inner_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.submatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
private lemma hsPair_left_ext {n : Type*} [Fintype n] [DecidableEq n]
    (A B : (Matrix n n ℂ)) (h : ∀ X, (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner A X = (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner B X) : A = B := by
  ext a b
  have hab := congrArg star (h (Matrix.single a b 1))
  simpa [matrix_inner_trace, Matrix.trace_single_mul, Matrix.conjTranspose_apply] using hab
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
private lemma amplification_adjoint_pair {d : ℕ} (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (X Y : (Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ)) :
    (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi)) Y) X = (Matrix.toMatrixInnerProductSpace (𝕜 := ℂ) 1 Matrix.PosSemidef.one).inner Y ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Phi) X) := by
  have hinner (X Y : (Matrix (Fin d) (Fin d) ℂ)) : inner ℂ X Y = (Y * X.conjTranspose).trace := by
    exact Matrix.trace_mul_comm X.conjTranspose Y
  rw [hsPair_blocks, hsPair_blocks]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [amplification_block,amplification_block]
  have h := hsAdjoint_inner_left Phi (Matrix.submatrix X (Prod.mk a) (Prod.mk b)) (Matrix.submatrix Y (Prod.mk a) (Prod.mk b))
  rw [hinner, hinner] at h
  simpa only [matrix_inner_trace] using h
end
section
variable {d : ℕ}
end
section
variable {d : ℕ}
private lemma hsAdjoint_star (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hPhi : ∀ X, Phi X.conjTranspose = (Phi X).conjTranspose)
    (Y : (Matrix (Fin d) (Fin d) ℂ)) :
    (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y.conjTranspose = ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y).conjTranspose := by
  ext a b
  simp only [Matrix.conjTranspose_apply, hsAdjoint_entry, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => M i j) (hPhi (Matrix.single a b 1))
  simp only [Matrix.conjTranspose_single, star_one, Matrix.conjTranspose_apply] at h
  rw [h]
  exact mul_comm _ _
private lemma amplify_star (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hPhi : ∀ X, Phi X.conjTranspose = (Phi X).conjTranspose)
    (X : (Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ)) : (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Phi) X.conjTranspose = ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Phi) X).conjTranspose := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [Matrix.conjTranspose_apply, amplification_apply]
  have h := congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => M i j) (hPhi (Matrix.submatrix X (Prod.mk b) (Prod.mk a)))
  exact h
end
section
variable {d : ℕ}
private lemma adjoint_twoPositive_of_star (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Phi))
    (hstar : ∀ X, Phi X.conjTranspose = (Phi X).conjTranspose) :
    (KPositive 2 _ ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi)) := by
  intro Y hY
  have hh : ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi)) Y).IsHermitian := by
    have h := amplify_star ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) (hsAdjoint_star Phi hstar) Y
    rw [hY.isHermitian.eq] at h
    exact h.symm
  apply psd_of_trace_pairing _ hh
  intro X hX
  have h := amplification_adjoint_pair Phi X Y
  rw [matrix_inner_trace, matrix_inner_trace] at h
  change (X * ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi)) Y).conjTranspose).trace =
    ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) Phi) X * Y.conjTranspose).trace at h
  rw [hh.eq, hY.isHermitian.eq] at h
  rw [Matrix.trace_mul_comm, h]
  exact trace_mul_psd_nonneg (h2 hX) hY
end
section
variable {d : ℕ}
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
lemma unital_iff_adjoint_tracePreserving (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    Phi 1 = 1 ↔ (∀ X, Matrix.trace (((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) X) = Matrix.trace X) := by
  have hinner (X Y : (Matrix (Fin d) (Fin d) ℂ)) : inner ℂ X Y = (Y * X.conjTranspose).trace := by
    exact Matrix.trace_mul_comm X.conjTranspose Y
  constructor
  · intro hu Y
    have h := hsAdjoint_inner_left Phi 1 Y
    rw [hinner, hinner] at h
    change (1 * ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y).conjTranspose).trace =
      (Phi 1 * Y.conjTranspose).trace at h
    rw [hu] at h
    simpa using congrArg star h
  · intro ht
    apply hsPair_left_ext
    intro Y
    have h := hsAdjoint_inner_left Phi 1 Y
    rw [hinner, hinner] at h
    change (1 * ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi Y).conjTranspose).trace =
      (Phi 1 * Y.conjTranspose).trace at h
    have hs := congrArg star h
    simp only [Matrix.one_mul, Matrix.trace_conjTranspose, star_star, ht Y] at hs
    rw [matrix_inner_trace, matrix_inner_trace]
    change (Y * (Phi 1).conjTranspose).trace = (Y * (1 : (Matrix (Fin d) (Fin d) ℂ)).conjTranspose).trace
    rw [Matrix.conjTranspose_one, Matrix.mul_one]
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at hs
    exact hs.symm
end
section
variable {d : ℕ}
lemma adjoint_twoPositive {d : ℕ} (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (h2 : (KPositive 2 _ Phi)) :
    (KPositive 2 _ ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi)) := by
  exact adjoint_twoPositive_of_star Phi h2 (twoPositive_star_preserving Phi h2)
end
section
variable {d : ℕ}
private lemma amplification_congruence {d : ℕ} (A : (Matrix (Fin d) (Fin d) ℂ))
    (X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ) :
    (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose)))) X =
      (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A) * X *
        (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) A).conjTranspose := by
  ext ⟨a,i⟩ ⟨b,j⟩
  have he : (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose)))) X (a,i) (b,j) =
      ∑ k : Fin d, ∑ l : Fin d, A i l * X (a,l) (b,k) * star (A j k) := by
    simp only [amplification_apply]
    change (∑ k : Fin d, (∑ l : Fin d, A i l * X (a,l) (b,k)) * star (A j k)) = _
    simp only [Finset.sum_mul]
  rw [he]
  simp only [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.conjTranspose_apply]
  simp_rw [Fintype.sum_prod_type]
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply, Finset.sum_mul]
lemma congrMap_twoPositive {d : ℕ} (A : (Matrix (Fin d) (Fin d) ℂ)) :
    (KPositive 2 _ ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose)))) := by
  intro X hX
  rw [amplification_congruence]
  exact hX.mul_mul_conjTranspose_same _
lemma twoPositive_comp {d : ℕ} (T S : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hT : (KPositive 2 _ T)) (hS : (KPositive 2 _ S)) : (KPositive 2 _ (T.comp S)) := by
  intro X hX
  have h := hT (hS hX)
  convert h using 1
  ext a b
  simp only [amplification_apply, LinearMap.comp_apply]
end
section
variable {d : ℕ}
theorem superoperator_trace_real_twoPositive {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Φ)) : (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Φ).im = 0 := by
  have hc (i j : Fin d) : star (Φ (Matrix.single i j 1) i j) =
      Φ (Matrix.single j i 1) j i := by
    let X := Matrix.vecMulVec (psiPlus j i) (star (psiPlus j i))
    have hX : X.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
    have h := (h2 hX).isHermitian.apply ((1 : Fin 2),j) ((0 : Fin 2),i)
    simpa [X, amplification_apply, block_plus] using h
  apply Complex.conj_eq_iff_im.mp
  rw [trace_standard]
  calc
    star (∑ i : Fin d, ∑ j : Fin d, Φ (Matrix.single i j 1) i j) =
        ∑ i : Fin d, ∑ j : Fin d, star (Φ (Matrix.single i j 1) i j) := by simp
    _ = ∑ i : Fin d, ∑ j : Fin d, Φ (Matrix.single j i 1) j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hc i j
    _ = ∑ i : Fin d, ∑ j : Fin d, Φ (Matrix.single i j 1) i j := Finset.sum_comm
end
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [Nontrivial A] [NormOneClass A]
private lemma positive_map_norm_four (U : (A →ₗ[ℂ] A))
    (hPos : ∀ X, 0 ≤ X → 0 ≤ U X)
    (X : A) : ‖U X‖ ≤ 4 * ‖U 1‖ * ‖X‖ := by
  let f := PositiveLinearMap.mk₀ U hPos
  obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg X
  change ‖f X‖ ≤ _
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul]
  apply norm_sum_le _ _ |>.trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  apply Finset.sum_le_sum (g := fun _ => ‖U 1‖ * ‖X‖) (fun i _ => ?_) |>.trans (by simp [mul_assoc])
  have h := PositiveLinearMap.norm_apply_le_of_nonneg f (y i) (hy_nonneg i)
  exact h.trans (mul_le_mul_of_nonneg_left (hy_norm i) (norm_nonneg (U 1)))
private lemma positive_power_fixed (U : (A →ₗ[ℂ] A))
    (hPos : ∀ X, 0 ≤ X → 0 ≤ U X)
    (ρ : A) (hFix : U ρ = ρ) (n : ℕ) :
    (∀ X, 0 ≤ X → 0 ≤ (U^n) X) ∧ (U^n) ρ = ρ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Module.End.iterate_succ']
    constructor
    · intro X hX
      exact hPos _ (ih.1 X hX)
    · change U ((U^n) ρ) = ρ
      rw [ih.2, hFix]
lemma faithful_fixed_eigenvalue_norm_le_one (U : (A →ₗ[ℂ] A))
    (hPos : ∀ X, 0 ≤ X → 0 ≤ U X)
    (ρ : A) (hρ : IsStrictlyPositive ρ) (hFix : U ρ = ρ)
    (z : ℂ) (hz : Module.End.HasEigenvalue U z) : ‖z‖ ≤ 1 := by
  obtain ⟨r,hr,hrρ⟩ := (CFC.exists_pos_algebraMap_le_iff
    ρ hρ.isSelfAdjoint).2 (fun z hz => hρ.spectrum_pos hz)
  have hIn : (1 : A) ≤ (r⁻¹ : ℝ) • ρ := by
    have h := smul_le_smul_of_nonneg_left hrρ (inv_nonneg.mpr hr.le)
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hr), one_smul] using h
  let K := 4 * ‖(r⁻¹ : ℝ) • ρ‖
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hb (n : ℕ) : ‖z‖ ^ n ≤ K := by
    obtain ⟨hp,hfix⟩ := positive_power_fixed U hPos ρ hFix n
    have horder := (PositiveLinearMap.mk₀ (U^n) hp).monotone' hIn
    change (U^n) 1 ≤ (U^n) ((r⁻¹ : ℝ) • ρ) at horder
    rw [LinearMap.map_smul_of_tower, hfix] at horder
    have hnorm : ‖(U^n) 1‖ ≤ ‖(r⁻¹ : ℝ) • ρ‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (hp 1 zero_le_one)
    have h := positive_map_norm_four (U^n) hp v
    have h' : ‖(U^n) v‖ ≤ K * ‖v‖ := by
      exact h.trans (by dsimp [K]; gcongr)
    rw [hv.pow_apply n, norm_smul, norm_pow] at h'
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv.2)).mp h'
  by_contra h
  have ht := tendsto_pow_atTop_atTop_of_one_lt (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop K).exists
  exact (not_lt_of_ge (hb n)) hn
end
section
variable {d : ℕ}
lemma root_mem_iff (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (z : ℂ) :
    z ∈ (Phi.charpoly.roots) ↔ Module.End.HasEigenvalue Phi z := by
  rw [ Polynomial.mem_roots Phi.charpoly_monic.ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
lemma roots_finite (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : {z : ℂ | z ∈ (Phi.charpoly.roots)}.Finite := by
  have he : {z : ℂ | z ∈ (Phi.charpoly.roots)} = (Phi.charpoly.roots.toFinset : Set ℂ) := by
    ext z
    simp only [ Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
  rw [he]
  exact Phi.charpoly.roots.toFinset.finite_toSet
lemma roots_nonempty [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    {z : ℂ | z ∈ (Phi.charpoly.roots)}.Nonempty := by
  obtain ⟨z,hz⟩ := Module.End.exists_eigenvalue Phi
  exact ⟨z,(root_mem_iff Phi z).mpr hz⟩
end
section
variable {d : ℕ}
private theorem extrema_close_of_roots_close {s t : Set ℂ}
    (hs : s.Finite) (ht : t.Finite) (hsn : s.Nonempty) (htn : t.Nonempty)
    {δ : ℝ}
    (hst : ∀ z ∈ s, ∃ w ∈ t, ‖z - w‖ ≤ δ)
    (hts : ∀ w ∈ t, ∃ z ∈ s, ‖w - z‖ ≤ δ) :
    |sInf ((Complex.re '' s)) - sInf ((Complex.re '' t))| ≤ δ ∧
      |sSup ((Complex.re '' s)) - sSup ((Complex.re '' t))| ≤ δ := by
  have hsR := hs.image Complex.re
  have htR := ht.image Complex.re
  have hsRn := hsn.image Complex.re
  have htRn := htn.image Complex.re
  have hminst : sInf ((Complex.re '' t)) ≤ sInf ((Complex.re '' s)) + δ := by
    obtain ⟨z, hz, heq⟩ := hsRn.csInf_mem hsR
    obtain ⟨w, hw, hzw⟩ := hst z hz
    have hnorm : |z.re - w.re| ≤ δ := by
      exact (Complex.abs_re_le_norm (z - w)).trans hzw
    have hmin := csInf_le htR.bddBelow (show w.re ∈ (Complex.re '' t) from ⟨w, hw, rfl⟩)
    linarith [(abs_le.mp hnorm).1]
  have hmints : sInf ((Complex.re '' s)) ≤ sInf ((Complex.re '' t)) + δ := by
    obtain ⟨w, hw, heq⟩ := htRn.csInf_mem htR
    obtain ⟨z, hz, hwz⟩ := hts w hw
    have hnorm : |w.re - z.re| ≤ δ := by
      exact (Complex.abs_re_le_norm (w - z)).trans hwz
    have hmin := csInf_le hsR.bddBelow (show z.re ∈ (Complex.re '' s) from ⟨z, hz, rfl⟩)
    linarith [(abs_le.mp hnorm).1]
  have hmaxst : sSup ((Complex.re '' s)) ≤ sSup ((Complex.re '' t)) + δ := by
    obtain ⟨z, hz, heq⟩ := hsRn.csSup_mem hsR
    obtain ⟨w, hw, hzw⟩ := hst z hz
    have hnorm : |z.re - w.re| ≤ δ := by
      exact (Complex.abs_re_le_norm (z - w)).trans hzw
    have hmax := le_csSup htR.bddAbove (show w.re ∈ (Complex.re '' t) from ⟨w, hw, rfl⟩)
    linarith [(abs_le.mp hnorm).2]
  have hmaxts : sSup ((Complex.re '' t)) ≤ sSup ((Complex.re '' s)) + δ := by
    obtain ⟨w, hw, heq⟩ := htRn.csSup_mem htR
    obtain ⟨z, hz, hwz⟩ := hts w hw
    have hnorm : |w.re - z.re| ≤ δ := by
      exact (Complex.abs_re_le_norm (w - z)).trans hwz
    have hmax := le_csSup hsR.bddAbove (show z.re ∈ (Complex.re '' s) from ⟨z, hz, rfl⟩)
    linarith [(abs_le.mp hnorm).2]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith
private theorem polynomial_extrema_close {p q : Polynomial ℂ}
    (hp : p.Monic) (hq : q.Monic) (hdeg : q.natDegree = p.natDegree)
    (hpn : (p.roots.toFinset : Set ℂ).Nonempty)
    (hqn : (q.roots.toFinset : Set ℂ).Nonempty)
    {ε R : ℝ} (hε : 0 < ε)
    (hcoeff : ∀ i : ℕ, ‖q.coeff i - p.coeff i‖ < ε)
    (hR : ∀ z : ℂ, z ∈ p.roots ∨ z ∈ q.roots → ‖z‖ ≤ R) :
    |sInf (Complex.re '' (p.roots.toFinset : Set ℂ)) -
      sInf (Complex.re '' (q.roots.toFinset : Set ℂ))| ≤
        ((p.natDegree + 1) * ε) ^ (p.natDegree : ℝ)⁻¹ * max R 1 ∧
    |sSup (Complex.re '' (p.roots.toFinset : Set ℂ)) -
      sSup (Complex.re '' (q.roots.toFinset : Set ℂ))| ≤
        ((p.natDegree + 1) * ε) ^ (p.natDegree : ℝ)⁻¹ * max R 1 := by
  apply extrema_close_of_roots_close
    p.roots.toFinset.finite_toSet q.roots.toFinset.finite_toSet hpn hqn
  · intro z hz
    have hz' : z ∈ p.roots := by simpa using hz
    obtain ⟨w, hw, hzw⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      hε ((Polynomial.mem_roots hp.ne_zero).mp hz') hp hq hdeg hcoeff
      (IsAlgClosed.splits q)
    refine ⟨w, by simpa using hw, hzw.le.trans ?_⟩
    gcongr
    exact hR z (Or.inl hz')
  · intro w hw
    have hw' : w ∈ q.roots := by simpa using hw
    have hcoeff' : ∀ i : ℕ, ‖p.coeff i - q.coeff i‖ < ε := by
      intro i
      simpa only [norm_sub_rev] using hcoeff i
    obtain ⟨z, hz, hwz⟩ := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      hε ((Polynomial.mem_roots hq.ne_zero).mp hw') hq hp hdeg.symm hcoeff'
      (IsAlgClosed.splits p)
    refine ⟨z, by simpa using hz, hwz.le.trans ?_⟩
    rw [hdeg]
    gcongr
    exact hR w (Or.inr hw')
private def polyRootMin (p : Polynomial ℂ) : ℝ :=
  sInf (Complex.re '' (p.roots.toFinset : Set ℂ))
private def polyRootMax (p : Polynomial ℂ) : ℝ :=
  sSup (Complex.re '' (p.roots.toFinset : Set ℂ))
end
section
variable {d : ℕ}
private theorem charpoly_coeff_continuous {n : Type*} [Fintype n] [DecidableEq n]
    (i : ℕ) : Continuous (fun A : Matrix n n ℂ => A.charpoly.coeff i) := by
  have hflat : Continuous (fun A : Matrix n n ℂ => fun x : n × n => A x.1 x.2) := by
    fun_prop
  have h := (MvPolynomial.continuous_eval
    ((Matrix.charpoly.univ ℂ n).coeff i)).comp hflat
  convert h using 1
  funext A
  exact (Matrix.charpoly.univ_coeff_eval₂Hom n (RingHom.id ℂ)
    (fun x : n × n => A x.1 x.2) i).symm
open scoped Matrix.Norms.L2Operator
private theorem charpoly_end_coeff_continuous {d : ℕ} (i : ℕ) :
    Continuous (fun L : (Matrix (Fin d) (Fin d) ℂ) →L[ℂ] (Matrix (Fin d) (Fin d) ℂ) => L.toLinearMap.charpoly.coeff i) := by
  let b := Matrix.stdBasis ℂ (Fin d) (Fin d)
  have hmat : Continuous (fun L : (Matrix (Fin d) (Fin d) ℂ) →L[ℂ] (Matrix (Fin d) (Fin d) ℂ) =>
      LinearMap.toMatrix b b L.toLinearMap) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro j
    simp only [LinearMap.toMatrix_apply]
    change Continuous (fun L : (Matrix (Fin d) (Fin d) ℂ) →L[ℂ] (Matrix (Fin d) (Fin d) ℂ) => b.coord a (L (b j)))
    have hcoord := LinearMap.continuous_of_finiteDimensional (b.coord a)
    fun_prop
  have h := (charpoly_coeff_continuous (n := Fin d × Fin d) i).comp hmat
  simpa only [Function.comp_def, LinearMap.charpoly_toMatrix] using h
private theorem root_norm_le_operator_norm {d : ℕ} [NeZero d]
    (L : (Matrix (Fin d) (Fin d) ℂ) →L[ℂ] (Matrix (Fin d) (Fin d) ℂ)) (z : ℂ)
    (hz : z ∈ L.toLinearMap.charpoly.roots) : ‖z‖ ≤ ‖L‖ := by
  exact spectrum.norm_le_norm_of_mem (𝕜 := ℂ) (a := L) (by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.mem_spectrum_iff_isRoot_charpoly L.toLinearMap z).mpr
      ((Polynomial.mem_roots L.toLinearMap.charpoly_monic.ne_zero).mp hz))
end
section
variable {d : ℕ}
private lemma positive_root_modulus (N : ℕ) (hN : 0 < N) (R : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ((N + 1 : ℝ) * δ) ^ (N : ℝ)⁻¹ * max R 1 < ε := by
  intro ε hε
  have hq : 0 < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hc : Continuous (fun δ : ℝ => ((N + 1 : ℝ) * δ) ^ (N : ℝ)⁻¹ * max R 1) :=
    ((Real.continuous_rpow_const hq.le).comp (continuous_const.mul continuous_id)).mul continuous_const
  have hzero : ((N + 1 : ℝ) * (0 : ℝ)) ^ (N : ℝ)⁻¹ * max R 1 = 0 := by
    simp [Real.zero_rpow hq.ne']
  have he : ∀ᶠ δ : ℝ in nhds 0,
      ((N + 1 : ℝ) * δ) ^ (N : ℝ)⁻¹ * max R 1 < ε :=
    (hc.tendsto 0).eventually (by simpa only [hzero] using (eventually_lt_nhds hε))
  obtain ⟨δ,hδ,hm⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by linarith, ?_⟩
  apply hm
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  linarith
lemma extrema_tendsto [NeZero d] {α : Type*} {l : Filter α}
    {A : α → (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ)} {B : (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ)}
    (hAB : Tendsto A l (nhds B)) :
    Tendsto (fun x => minReSpectrum (A x).toLinearMap) l
      (nhds (minReSpectrum B.toLinearMap)) ∧
    Tendsto (fun x => maxReSpectrum (A x).toLinearMap) l
      (nhds (maxReSpectrum B.toLinearMap)) := by
  let p := B.toLinearMap.charpoly
  let q := fun x => (A x).toLinearMap.charpoly
  have hp : p.Monic := LinearMap.charpoly_monic _
  have hq : ∀ x, (q x).Monic := fun x => LinearMap.charpoly_monic _
  have hdeg : ∀ x, (q x).natDegree = p.natDegree := by
    intro x
    simp only [q,p,LinearMap.charpoly_natDegree]
  have hN : 0 < p.natDegree := by
    rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  have hpn : (p.roots.toFinset : Set ℂ).Nonempty := by
    obtain ⟨z,hz⟩ := roots_nonempty B.toLinearMap
    exact ⟨z, by simpa only [p,Set.mem_setOf_eq,Finset.mem_coe,Multiset.mem_toFinset] using hz⟩
  have hqn : ∀ x, ((q x).roots.toFinset : Set ℂ).Nonempty := by
    intro x
    obtain ⟨z,hz⟩ := roots_nonempty (A x).toLinearMap
    exact ⟨z, by simpa only [q,Set.mem_setOf_eq,Finset.mem_coe,Multiset.mem_toFinset] using hz⟩
  let R := ‖B‖ + 1
  have hR : ∀ᶠ x in l, ∀ z : ℂ, z ∈ p.roots ∨ z ∈ (q x).roots → ‖z‖ ≤ R := by
    have hn : ∀ᶠ x in l, ‖A x‖ < ‖B‖ + 1 :=
      hAB.norm.eventually (eventually_lt_nhds (by linarith : ‖B‖ < ‖B‖ + 1))
    filter_upwards [hn] with x hx z hz
    rcases hz with hz | hz
    · exact (root_norm_le_operator_norm B z hz).trans (by dsimp [R]; linarith)
    · exact (root_norm_le_operator_norm (A x) z hz).trans hx.le
  have hcoeff : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ i : ℕ,
      ‖(q x).coeff i - p.coeff i‖ < ε := by
    intro ε hε
    have hc : ∀ i, Tendsto (fun x => (q x).coeff i - p.coeff i) l (nhds 0) := by
      intro i
      have ht := ((charpoly_end_coeff_continuous i).tendsto B |>.comp hAB).sub_const (p.coeff i)
      simpa only [Function.comp_def,p,q,sub_self] using ht
    have he : ∀ᶠ x in l, ∀ i ∈ Finset.range (p.natDegree + 1),
        ‖(q x).coeff i - p.coeff i‖ < ε := by
      rw [Finset.eventually_all]

      intro i hi
      exact (hc i).norm.eventually (by simpa using eventually_lt_nhds hε)
    filter_upwards [he] with x hx i
    by_cases hi : i < p.natDegree + 1
    · exact hx i (Finset.mem_range.mpr hi)
    · have hpi : p.natDegree < i := by omega
      have hqi : (q x).natDegree < i := by rw [hdeg]; exact hpi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hpi,
        Polynomial.coeff_eq_zero_of_natDegree_lt hqi,sub_self,norm_zero]
      exact hε
  have hmod := positive_root_modulus p.natDegree hN R
  have hsets (C : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : {z : ℂ | z ∈ (C.charpoly.roots)} =
      (C.charpoly.roots.toFinset : Set ℂ) := by ext z; simp
  have hMin (C : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : minReSpectrum C = polyRootMin C.charpoly := by
    rw [minReSpectrum,hsets]; rfl
  have hMax (C : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : maxReSpectrum C = polyRootMax C.charpoly := by
    rw [maxReSpectrum,hsets]; rfl
  constructor
  · simp_rw [hMin]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hm⟩ := hmod ε hε
    filter_upwards [hR,hcoeff δ hδ] with x hx hc
    have hclose := polynomial_extrema_close hp (hq x) (hdeg x) hpn (hqn x) hδ hc hx
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (by simpa only [polyRootMin,abs_sub_comm] using hclose.1) hm
  · simp_rw [hMax]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hm⟩ := hmod ε hε
    filter_upwards [hR,hcoeff δ hδ] with x hx hc
    have hclose := polynomial_extrema_close hp (hq x) (hdeg x) hpn (hqn x) hδ hc hx
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (by simpa only [polyRootMax,abs_sub_comm] using hclose.2) hm
end
section
variable {d : ℕ}
lemma superTrace_continuous {d : ℕ} :
    Continuous (fun L : (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ) => (LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) L.toLinearMap)) := by
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ))).comp (ContinuousLinearMap.coeLM ℂ))
end
end D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
