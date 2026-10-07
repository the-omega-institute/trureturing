/- GID: D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The spectral trace bound for two-positive trace-preserving maps. -/

/- Judgement:
   admission_basis: escape-witness.
   Module escape_witness: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   Direct frozen dependencies:
   D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists: statement_id sha256:b51576d39e34c406189cfe25b2e79357c5dc966f97a9664c52ab8dadbf50d12b.
   Information-escape registration is paused under CLAUDE.md §3.9.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.SourceTheorem1Bound: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.SourceTheorem1Goal, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_rescaling_is_algebraic.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.reuse_channel_fixed_state: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.faithful_of_strict_fixed: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.SourceTheorem1Goal: proof_shape: not-applicable; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.epsilon_route_conditional.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.col_stochastic_root_norm_le_one: proof_shape: content; escape_witness: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.col_stochastic_root_norm_le_one; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.col_stochastic_trace_le.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.multiset_real_sum_le_distinguished: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.col_stochastic_trace_le.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.col_stochastic_trace_le: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_case_from_transition.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.realEigenBound: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_case_from_transition, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_case_from_transition: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hermitian_eigen_of_star_preserving: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.unitary_conj_apply: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hermitian_diagonal_eigen.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hermitian_diagonal_eigen: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congr_inner: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_congr.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_congr: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_comp: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congr_comp_apply: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congr_inverse_apply.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congr_inverse_apply: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congrEquiv, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_supertrace.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_tracePreserving: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.congrEquiv: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_conjugate: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart_conjugate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart_conjugate, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedSymmetricPart_conjugate: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.symmetricPart_symmetric: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.bendixson_real_eigenvalue.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.symmetricPart_rayleigh_eigen: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.bendixson_real_eigenvalue.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.bendixson_real_eigenvalue: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hasEigenvalue_conj_iff: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_toMatrix: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_charpoly, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_trace.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_charpoly: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_roots.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_trace: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.minReSpectrum_attained: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.hsAdjoint_roots: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.realParts_hsAdjoint.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.realParts_hsAdjoint: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_hsAdjoint.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_hsAdjoint: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.extrema_conj: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.faithful_fourth_roots: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unital_similarity_certificate.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.unitary_conj_eq_congr: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.unitary_congr_trace: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.transition_diagonal_eigen: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound: proof_shape: content; escape_witness: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_eigen_trace_bound; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weightedAdjoint_supertrace: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful: proof_shape: content; escape_witness: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_faithful; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized: proof_shape: not-applicable; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_twoPositive, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_tracePreserving, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_strict, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_tendsto, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_twoPositive: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_tracePreserving: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed, D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_strict: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_faithful_fixed: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.depolarized_tendsto: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_limit_preserves_bound: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general, _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.real_limit_preserves_bound_within: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.result.
   D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general: proof_shape: content; escape_witness: D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.theorem1_general; consumer: _private.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.0.D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.twoPositive_spectralBound.
   _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.selfAdjointPart_complex: proof_shape: bind-only; escape_witness: none; consumer: _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.symmetricPart_symmetric, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.symmetricPart_rayleigh_eigen, _private.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.0.D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound.weighted_bendixson.
-/
import D5.S3.Quantum.ChannelFixedState
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Set Filter Module.End
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal NNReal
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
namespace D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
variable {d : ℕ}
section
variable {d : ℕ}
def SourceTheorem1Bound {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Φ)).re ≤
    (d : ℝ) * minReSpectrum Φ + ((d : ℝ)^2 - d)
private theorem reuse_channel_fixed_state {d : ℕ} [NeZero d]
    (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (hPos : ∀ rho : (Matrix (Fin d) (Fin d) ℂ), rho.PosSemidef → (Φ rho).PosSemidef)
    (hTP : (∀ X, Matrix.trace (Φ X) = Matrix.trace X)) :
    ∃ rho : (Matrix (Fin d) (Fin d) ℂ), rho.PosSemidef ∧ Matrix.trace rho = 1 ∧ Φ rho = rho := by
  exact D5.S3.Quantum.ChannelFixedState.channel_fixed_state_exists Φ hPos hTP
private theorem faithful_of_strict_fixed {d : ℕ} (T : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (hStrict : ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → X ≠ 0 → (T X).PosDef)
    (rho : (Matrix (Fin d) (Fin d) ℂ)) (hPos : rho.PosSemidef) (hTrace : Matrix.trace rho = 1)
    (hFix : T rho = rho) : rho.PosDef := by
  rw [← hFix]
  apply (hStrict rho hPos ?_)
  intro hzero
  rw [hzero] at hTrace
  simp at hTrace
def SourceTheorem1Goal : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ),
    (KPositive 2 _ Φ) → (∀ X, Matrix.trace (Φ X) = Matrix.trace X) → SourceTheorem1Bound Φ
end
section
variable {d : ℕ}
end
section
variable {d : ℕ}
private lemma col_stochastic_root_norm_le_one {d : ℕ} [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T ∈ Matrix.colStochastic ℝ (Fin d))
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ ((T.map (algebraMap ℝ ℂ)) : Matrix (Fin d) (Fin d) ℂ)) :
    ‖μ‖ ≤ 1 := by
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (T.map (algebraMap ℝ ℂ))) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hspec).exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hveq : Matrix.mulVec (T.map (algebraMap ℝ ℂ)) v = μ • v := by
    have hveq' := Module.End.mem_eigenspace_iff.mp hv.1
    simpa [Matrix.toLin'_apply] using hveq'
  let s : ℝ := ∑ i : Fin d, ‖v i‖
  have hspos : 0 < s := by
    dsimp [s]
    have : ∃ i : Fin d, v i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv0
      funext i
      exact h i
    obtain ⟨i, hi⟩ := this
    have hi' : 0 < ‖v i‖ := norm_pos_iff.mpr hi
    exact lt_of_lt_of_le hi' (Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i))
  have hcoord (i : Fin d) :
      ‖μ‖ * ‖v i‖ = ‖∑ j : Fin d, (algebraMap ℝ ℂ) (T i j) * v j‖ := by
    have hi := congrArg (fun z : ℂ => ‖z‖) (congrFun hveq i)
    symm
    simpa [Matrix.mulVec, dotProduct, smul_eq_mul, norm_mul] using hi
  have hsum :
      ∑ i : Fin d, ‖∑ j : Fin d, (algebraMap ℝ ℂ) (T i j) * v j‖ ≤ s := by
    calc
      ∑ i : Fin d, ‖∑ j : Fin d, (algebraMap ℝ ℂ) (T i j) * v j‖ ≤
          ∑ i : Fin d, ∑ j : Fin d, ‖(algebraMap ℝ ℂ) (T i j) * v j‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_sum_le _ _
      _ = ∑ j : Fin d, ‖v j‖ * ∑ i : Fin d, T i j := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hnon : ∀ i j : Fin d, 0 ≤ T i j := (Matrix.mem_colStochastic_iff_sum.mp hT).1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
            have hnorm : ∀ i : Fin d, ‖(algebraMap ℝ ℂ) (T i j)‖ = T i j := by
              intro i
              simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnon i j)]
            simp_rw [hnorm]
            ring
      _ = s := by
            simp [s, Matrix.sum_col_of_mem_colStochastic hT]
  have hsum_eq : ‖μ‖ * s ≤ s := by
    calc
      ‖μ‖ * s = ∑ i : Fin d, ‖μ‖ * ‖v i‖ := by simp [s, Finset.mul_sum]
      _ = ∑ i : Fin d, ‖∑ j : Fin d, (algebraMap ℝ ℂ) (T i j) * v j‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcoord i
      _ ≤ s := hsum
  nlinarith
open scoped ComplexOrder MatrixOrder
private lemma multiset_real_sum_le_distinguished {d : ℕ} {s : Multiset ℂ} {r : ℝ}
    (hr : (r : ℂ) ∈ s) (hb : ∀ z ∈ s, z.re ≤ 1) (hc : s.card = d) :
    (s.map Complex.re).sum ≤ r + (d : ℝ) - 1 := by
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hr
  rw [ht, Multiset.map_cons, Multiset.sum_cons] at ⊢
  rw [ht, Multiset.card_cons] at hc
  have hbt : ∀ z ∈ t, z.re ≤ 1 := by
    intro z hz
    exact hb z (by rw [ht]; exact Multiset.mem_cons_of_mem hz)
  have hsum : (t.map Complex.re).sum ≤ (t.card : ℝ) := by
    have h := Multiset.sum_le_card_nsmul (t.map Complex.re) (1 : ℝ) (by
      intro z hz
      rcases (Multiset.mem_map.mp hz) with ⟨w, hw, heq⟩
      subst z
      exact hbt w hw)
    simpa [nsmul_eq_mul] using h
  change r + (t.map Complex.re).sum ≤ r + (d : ℝ) - 1
  have hc' : (t.card : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hc
  nlinarith [hsum, hc']
private lemma col_stochastic_trace_le {d : ℕ} [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T ∈ Matrix.colStochastic ℝ (Fin d))
    {r : ℝ}
    (hr : (r : ℂ) ∈ (T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots) :
    T.trace ≤ r + (d : ℝ) - 1 := by
  have hcard : ((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots).card = d := by
    have hs := (IsAlgClosed.splits ((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly)).natDegree_eq_card_roots
    simpa using hs.symm
  have hb : ∀ z ∈ ((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots), z.re ≤ 1 := by
    intro z hz
    have hzabs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hzbound : ‖z‖ ≤ 1 := col_stochastic_root_norm_le_one T hT
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
        ((Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero)).mp hz))
    exact (le_abs_self z.re).trans (hzabs.trans hzbound)
  have hsum := multiset_real_sum_le_distinguished hr hb hcard
  have htrace := Matrix.trace_eq_sum_roots_charpoly (T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ)
  have hsumre := congrArg Complex.re htrace
  have hmap : (((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots).map Complex.re).sum =
      (((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.sum).re) := by
    induction ((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots) using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simp [ih]
  have hsum_real : (((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.sum).re) ≤ r + (d : ℝ) - 1 := by
    rw [← hmap]
    exact hsum
  have htraceR : T.trace = (((T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).trace).re) := by
    simp [Matrix.trace]
  rw [htraceR, hsumre]
  exact hsum_real
end
section
variable {d : ℕ}
private def realEigenBound {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (lam : ℝ) : Prop :=
  (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Φ).re ≤ (d : ℝ) * lam + (d : ℝ)^2 - d
private theorem real_eigen_case_from_transition {d : ℕ} [NeZero d]
    (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (T : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ)
    (htrace : (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Φ).re ≤ (d : ℝ) * T.trace)
    (hT : T ∈ Matrix.colStochastic ℝ (Fin d))
    (hroot : (lam : ℂ) ∈ (T.map (algebraMap ℝ ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly.roots) :
    realEigenBound Φ lam := by
  have hTbound := col_stochastic_trace_le T hT hroot
  dsimp [realEigenBound]
  nlinarith
end
section
variable {d : ℕ}
private theorem hermitian_eigen_of_star_preserving {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (lam : ℝ)
    (hstar : ∀ Y : (Matrix (Fin d) (Fin d) ℂ), Φ (Matrix.conjTranspose Y) = Matrix.conjTranspose (Φ Y))
    {Y : (Matrix (Fin d) (Fin d) ℂ)} (hY : Y ≠ 0) (hEig : Φ Y = (lam : ℂ) • Y) :
    ∃ X : (Matrix (Fin d) (Fin d) ℂ), X.IsHermitian ∧ X ≠ 0 ∧ Φ X = (lam : ℂ) • X := by
  let A : (Matrix (Fin d) (Fin d) ℂ) := Y + Matrix.conjTranspose Y
  let B : (Matrix (Fin d) (Fin d) ℂ) := Complex.I • (Y - Matrix.conjTranspose Y)
  have hAherm : A.IsHermitian := by
    dsimp [A]
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    ring
  have hBherm : B.IsHermitian := by
    dsimp [B]
    apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    ring
  have hstarEig : Φ (Matrix.conjTranspose Y) = (lam : ℂ) • Matrix.conjTranspose Y := by
    rw [hstar, hEig, Matrix.conjTranspose_smul]
    simp
  have hAEig : Φ A = (lam : ℂ) • A := by
    dsimp [A]
    rw [map_add, hEig, hstarEig]
    simp [smul_add]
  have hBEig : Φ B = (lam : ℂ) • B := by
    dsimp [B]
    rw [map_smul, map_sub, hEig, hstarEig]
    simp only [smul_sub]
    ext i j
    simp [smul_eq_mul]
    ring
  by_cases hAz : A ≠ 0
  · exact ⟨A, hAherm, hAz, hAEig⟩
  · have hBz : B ≠ 0 := by
      intro hB
      apply hY
      have hdiff : Y - Matrix.conjTranspose Y = 0 := by
        dsimp [B] at hB
        simpa [smul_eq_zero] using hB
      have hsum : Y + Matrix.conjTranspose Y = 0 := by
        exact not_ne_iff.mp hAz
      ext i j
      have h1 : Y i j - Matrix.conjTranspose Y i j = 0 := by
        simpa using congr_fun (congr_fun hdiff i) j
      have h2 : Y i j + Matrix.conjTranspose Y i j = 0 := by
        simpa using congr_fun (congr_fun hsum i) j
      change Y i j = 0
      linear_combination (h2 + h1) / 2
    exact ⟨B, hBherm, hBz, hBEig⟩
end
section
variable {d : ℕ}
private lemma unitary_conj_apply {d : ℕ} [DecidableEq (Fin d)]
    (u : Matrix.unitaryGroup (Fin d) ℂ) (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (X : (Matrix (Fin d) (Fin d) ℂ)) :
    LinearEquiv.conj (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u).toAlgEquiv.toLinearEquiv Phi ((Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) u) X) =
      (Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) u) (Phi X) := by
  simp only [ LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply]
  exact congrArg (fun M => (Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) u) (Phi M))
    ((Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) u).symm_apply_apply X)
private lemma hermitian_diagonal_eigen {d : ℕ} [DecidableEq (Fin d)]
    (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (X : (Matrix (Fin d) (Fin d) ℂ)) (lam : ℝ)
    (hX : X.IsHermitian)
    (he : Phi X = (lam : ℂ) • X) :
    let u := hX.eigenvectorUnitary
    LinearEquiv.conj (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) (star u)).toAlgEquiv.toLinearEquiv Phi
      (Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) =
      (lam : ℂ) • Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
  dsimp only
  have hdiag := hX.conjStarAlgAut_star_eigenvectorUnitary
  change (Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) (star hX.eigenvectorUnitary)) X =
      Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) at hdiag
  rw [← hdiag]
  rw [unitary_conj_apply]
  rw [he, map_smul]
end
section
variable {d : ℕ}
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
private lemma congr_inner (A X Y : (Matrix (Fin d) (Fin d) ℂ)) :
    inner ℂ ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose)) X) Y = inner ℂ X ((LinearMap.mulLeftRight ℂ (A.conjTranspose, A.conjTranspose.conjTranspose)) Y) := by
  have hinner (X Y : (Matrix (Fin d) (Fin d) ℂ)) : inner ℂ X Y = (Y * X.conjTranspose).trace := by
    exact Matrix.trace_mul_comm X.conjTranspose Y
  rw [hinner, hinner]
  change (Y * (A * X * A.conjTranspose).conjTranspose).trace =
    ((A.conjTranspose * Y * (A.conjTranspose).conjTranspose) * X.conjTranspose).trace
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (Y * A) X.conjTranspose A.conjTranspose)
private lemma hsAdjoint_congr (A : (Matrix (Fin d) (Fin d) ℂ)) :
    (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose))) = (LinearMap.mulLeftRight ℂ (A.conjTranspose, A.conjTranspose.conjTranspose)) := by
  apply LinearMap.ext
  intro Y
  apply ext_inner_left ℂ
  intro X
  apply star_injective
  have hA : star (inner ℂ X ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose))) Y)) =
      inner ℂ ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose))) Y) X :=
    inner_conj_symm (𝕜 := ℂ) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((LinearMap.mulLeftRight ℂ (A, A.conjTranspose))) Y) X
  have hB : star (inner ℂ X ((LinearMap.mulLeftRight ℂ (A.conjTranspose, A.conjTranspose.conjTranspose)) Y)) =
      inner ℂ ((LinearMap.mulLeftRight ℂ (A.conjTranspose, A.conjTranspose.conjTranspose)) Y) X :=
    inner_conj_symm (𝕜 := ℂ) ((LinearMap.mulLeftRight ℂ (A.conjTranspose, A.conjTranspose.conjTranspose)) Y) X
  rw [hA, hB]
  rw [hsAdjoint_inner_left]
  rw [congr_inner]
  simp only [Matrix.conjTranspose_conjTranspose]
private lemma hsAdjoint_comp (P Q : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) (P.comp Q) = ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Q).comp ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) P) := by
  let hfd : @Module.Finite ℂ ((Matrix (Fin d) (Fin d) ℂ)) _ _
      (@NormedSpace.toModule ℂ ((Matrix (Fin d) (Fin d) ℂ)) _ (Matrix.frobeniusSeminormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) Matrix.frobeniusNormedSpace) := by
    exact FiniteDimensional.finiteDimensional_pi' ℂ _
  exact @LinearMap.adjoint_comp ℂ ((Matrix (Fin d) (Fin d) ℂ)) ((Matrix (Fin d) (Fin d) ℂ)) ((Matrix (Fin d) (Fin d) ℂ))
    _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner hsInner hfd hfd hfd P Q
end
section
variable {d : ℕ}
private lemma congr_comp_apply (A B X : (Matrix (Fin d) (Fin d) ℂ)) :
    (LinearMap.mulLeftRight ℂ (A, A.conjTranspose)) ((LinearMap.mulLeftRight ℂ (B, B.conjTranspose)) X) = (LinearMap.mulLeftRight ℂ ((A * B), (A * B).conjTranspose)) X := by
  simp only [LinearMap.mulLeftRight_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_mul]
  noncomm_ring
private lemma congr_inverse_apply (W V X : (Matrix (Fin d) (Fin d) ℂ)) (hWV : W * V = 1) :
    (LinearMap.mulLeftRight ℂ (W, W.conjTranspose)) ((LinearMap.mulLeftRight ℂ (V, V.conjTranspose)) X) = X := by
  rw [congr_comp_apply, hWV]
  simp [LinearMap.mulLeftRight_apply]
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
private lemma weightedAdjoint_tracePreserving (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (W V rho : (Matrix (Fin d) (Fin d) ℂ))
    (hW : W.IsHermitian) (hV : V.IsHermitian) (hVW : V * W = 1)
    (hrho : W * W = rho) (hfixed : Phi rho = rho) :
    (∀ X, Matrix.trace ((weightedAdjoint Phi W V) X) = Matrix.trace X) := by
  have hinner (X Y : (Matrix (Fin d) (Fin d) ℂ)) : inner ℂ X Y = (Y * X.conjTranspose).trace := by
    exact Matrix.trace_mul_comm X.conjTranspose Y
  intro X
  let F : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) := (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi
  have hWV : W * V = 1 := mul_eq_one_comm.mp hVW
  have hr : rho.IsHermitian := by rw [← hrho]; simpa [hW.eq] using Matrix.isHermitian_mul_conjTranspose_self W
  let Z := (LinearMap.mulLeftRight ℂ (V, V.conjTranspose)) X
  have hp : inner ℂ (F Z) rho = inner ℂ Z (Phi rho) := hsAdjoint_inner_left Phi rho Z
  rw [hinner, hinner] at hp
  change (rho * (F Z).conjTranspose).trace = (Phi rho * Z.conjTranspose).trace at hp
  rw [hfixed] at hp
  have hs := congrArg star hp
  simp only [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hr.eq] at hs
  change (W * F Z * W.conjTranspose).trace = X.trace
  rw [hW.eq]
  calc
    (W * F Z * W).trace = (F Z * rho).trace := by
      rw [← hrho]
      simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (F Z) W W).symm
    _ = (Z * rho).trace := hs
    _ = X.trace := by
      change (V * X * V.conjTranspose * rho).trace = X.trace
      rw [hV.eq, ← hrho]
      calc
        (V * X * V * (W * W)).trace = (X * (V * (W * W) * V)).trace := by
          simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle (X * V) (W * W) V).symm
        _ = X.trace := by
          have hvw : V * (W * W) * V = 1 := by
            calc
              V * (W * W) * V = (V * W) * (W * V) := by noncomm_ring
              _ = 1 := by rw [hVW, hWV, Matrix.one_mul]
          rw [hvw, Matrix.mul_one]
end
section
variable {d : ℕ}
private lemma weightedAdjoint_twoPositive {d : ℕ} (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (W V : (Matrix (Fin d) (Fin d) ℂ)) :
    (KPositive 2 _ (weightedAdjoint Phi W V)) := by
  exact twoPositive_comp _ _ (congrMap_twoPositive W)
    (twoPositive_comp _ _ (adjoint_twoPositive Phi h2)
      (congrMap_twoPositive V))
end
section
variable {d : ℕ}
def congrEquiv (R S : (Matrix (Fin d) (Fin d) ℂ)) (hRS : R * S = 1) (hSR : S * R = 1) :
    (Matrix (Fin d) (Fin d) ℂ) ≃ₗ[ℂ] (Matrix (Fin d) (Fin d) ℂ) :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeftRight ℂ (R, R.conjTranspose))
    (LinearMap.mulLeftRight ℂ (S, S.conjTranspose))
    (by apply LinearMap.ext; intro X; exact congr_inverse_apply R S X hRS)
    (by apply LinearMap.ext; intro X; exact congr_inverse_apply S R X hSR)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
private lemma weightedAdjoint_conjugate (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (R S : (Matrix (Fin d) (Fin d) ℂ))
    (hR : R.IsHermitian) (hS : S.IsHermitian) (hRS : R * S = 1) (hSR : S * R = 1) :
    (congrEquiv R S hRS hSR).conj (weightedAdjoint Phi (S * S) (R * R)) =
      (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((congrEquiv R S hRS hSR).conj Phi) := by
  let CR : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    LinearMap.mulLeftRight ℂ (R, R.conjTranspose)
  let CS : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    LinearMap.mulLeftRight ℂ (S, S.conjTranspose)
  have hCR : (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) CR = CR := by
    change (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) (LinearMap.mulLeftRight ℂ (R, R.conjTranspose)) = _
    rw [hsAdjoint_congr R, hR.eq]
  have hCS : (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) CS = CS := by
    change (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) (LinearMap.mulLeftRight ℂ (S, S.conjTranspose)) = _
    rw [hsAdjoint_congr S, hS.eq]
  have hAdj : (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) (CR.comp (Phi.comp CS)) = CS.comp (((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi).comp CR) := by
    rw [hsAdjoint_comp CR (Phi.comp CS), hsAdjoint_comp Phi CS, hCR, hCS]
    rfl
  apply LinearMap.ext
  intro X
  change CR (weightedAdjoint Phi (S * S) (R * R) (CS X)) =
    (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) (CR.comp (Phi.comp CS)) X
  rw [hAdj]
  simp only [CR, CS, weightedAdjoint, LinearMap.comp_apply, LinearMap.mulLeftRight_apply]
  have hS2 : (S * S).conjTranspose = S * S := by rw [Matrix.conjTranspose_mul, hS.eq]
  have hR2 : (R * R).conjTranspose = R * R := by rw [Matrix.conjTranspose_mul, hR.eq]
  have hin : (R * R) * (S * X * S) * (R * R) = R * X * R := by
    calc
      (R * R) * (S * X * S) * (R * R) = R * (R * S) * X * (S * R) * R := by noncomm_ring
      _ = R * X * R := by rw [hRS, hSR]; simp
  rw [hR.eq, hS.eq, hR2, hS2, hin]
  calc
    R * ((S * S) * (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi (R * X * R) * (S * S)) * R =
      (R * S) * S * (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi (R * X * R) * S * (S * R) := by noncomm_ring
    _ = S * (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi (R * X * R) * S := by rw [hRS, hSR]; simp
private def weightedSymmetricPart (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (W V : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  (1 / 2 : ℂ) • (Phi + weightedAdjoint Phi W V)
private lemma weightedSymmetricPart_conjugate (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (R S : (Matrix (Fin d) (Fin d) ℂ))
    (hR : R.IsHermitian) (hS : S.IsHermitian) (hRS : R * S = 1) (hSR : S * R = 1) :
    (congrEquiv R S hRS hSR).conj (weightedSymmetricPart Phi (S * S) (R * R)) =
      (1 / 2 : ℂ) • (((congrEquiv R S hRS hSR).conj Phi) + (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) ((congrEquiv R S hRS hSR).conj Phi)) := by
  simp only [weightedSymmetricPart, map_smul, map_add]
  rw [weightedAdjoint_conjugate Phi R S hR hS hRS hSR]
end
section
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
private lemma selfAdjointPart_complex (A : E →ₗ[ℂ] E) :
    (selfAdjointPart ℝ A).val = (1 / 2 : ℂ) • (A + A.adjoint) := by
  change (⅟2 : ℝ) • (A + A.adjoint) = (1 / 2 : ℂ) • (A + A.adjoint)
  rw [← algebraMap_smul ℂ (⅟2 : ℝ) (A + A.adjoint)]
  norm_num [invOf_eq_inv]
private lemma symmetricPart_symmetric (A : E →ₗ[ℂ] E) : ((selfAdjointPart ℝ A).val).IsSymmetric := by
  intro x y
  simp only [selfAdjointPart_complex, LinearMap.smul_apply, LinearMap.add_apply,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    exact star_ofNat 2
  norm_num [htwo]
  ring
private lemma symmetricPart_rayleigh_eigen (A : E →ₗ[ℂ] E) {mu : ℂ} {v : E}
    (hv : v ≠ 0) (he : A v = mu • v) :
    (inner ℂ ((selfAdjointPart ℝ A).val v) v).re / ‖v‖ ^ 2 = mu.re := by
  simp only [selfAdjointPart_complex, LinearMap.smul_apply, LinearMap.add_apply,
    inner_smul_left, inner_add_left, LinearMap.adjoint_inner_left,
    he, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [map_div₀, map_one, map_ofNat, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  norm_num [← Complex.ofReal_pow]
  field_simp [norm_ne_zero_iff.mpr hv]
  <;> ring
private lemma bendixson_real_eigenvalue (A : E →ₗ[ℂ] E) :
    ∃ r : ℝ, HasEigenvalue ((selfAdjointPart ℝ A).val) (r : ℂ) ∧
      ∀ mu : ℂ, HasEigenvalue A mu → r ≤ mu.re := by
  let H := (selfAdjointPart ℝ A).val
  let r : ℝ := ⨅ x : {x : E // x ≠ 0}, (inner ℂ (H x) x).re / ‖(x : E)‖ ^ 2
  have hH : H.IsSymmetric := symmetricPart_symmetric A
  have hb : BddBelow (range (fun x : {x : E // x ≠ 0} =>
      (inner ℂ (H x) x).re / ‖(x : E)‖ ^ 2)) := by
    refine ⟨-‖H.toContinuousLinearMap‖, ?_⟩
    rintro _ ⟨x,rfl⟩
    exact (abs_le.mp (H.toContinuousLinearMap.rayleighQuotient_le_norm x)).1
  refine ⟨r, hH.hasEigenvalue_iInf_of_finiteDimensional, ?_⟩
  intro mu hmu
  obtain ⟨v,hv⟩ := hmu.exists_hasEigenvector
  have hle := ciInf_le hb (⟨v,hv.2⟩ : {x : E // x ≠ 0})
  have he : A v = mu • v := Module.End.mem_eigenspace_iff.mp hv.1
  simpa only [H, symmetricPart_rayleigh_eigen A hv.2 he] using hle
end
section
variable {d : ℕ}
attribute [local instance 2000] Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedSpace hsInner
private lemma hasEigenvalue_conj_iff (e : (Matrix (Fin d) (Fin d) ℂ) ≃ₗ[ℂ] (Matrix (Fin d) (Fin d) ℂ))
    (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (mu : ℂ) :
    Module.End.HasEigenvalue (e.conj Phi) mu ↔ Module.End.HasEigenvalue Phi mu := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    LinearEquiv.charpoly_conj, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
private lemma weighted_bendixson [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (R S : (Matrix (Fin d) (Fin d) ℂ))
    (hR : R.IsHermitian) (hS : S.IsHermitian) (hRS : R * S = 1) (hSR : S * R = 1) :
    ∃ r : ℝ, Module.End.HasEigenvalue (weightedSymmetricPart Phi (S * S) (R * R)) (r : ℂ) ∧
      ∀ mu : ℂ, Module.End.HasEigenvalue Phi mu → r ≤ mu.re := by
  let e := congrEquiv R S hRS hSR
  let A := e.conj Phi
  obtain ⟨r,hr,hb⟩ := bendixson_real_eigenvalue A
  have hh : e.conj (weightedSymmetricPart Phi (S * S) (R * R)) = (selfAdjointPart ℝ A).val := by
    rw [selfAdjointPart_complex]
    exact weightedSymmetricPart_conjugate Phi R S hR hS hRS hSR
  refine ⟨r, ?_, ?_⟩
  · rw [← hasEigenvalue_conj_iff e, hh]
    exact hr
  · intro mu hmu
    apply hb
    exact (hasEigenvalue_conj_iff e Phi mu).mpr hmu
end
section
variable {d : ℕ}
private lemma hsAdjoint_toMatrix (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d))
      (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) =
    (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d))
      (Matrix.stdBasis ℂ (Fin d) (Fin d)) Phi).conjTranspose := by
  ext ⟨a,b⟩ ⟨c,e⟩
  simp [LinearMap.toMatrix_apply, Matrix.stdBasis, Matrix.conjTranspose_apply,
    ← Matrix.single_eq_of_single_single, hsAdjoint_entry,
    Matrix.single, Pi.single_apply, ite_and]
private lemma hsAdjoint_charpoly (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi).charpoly = Phi.charpoly.map (starRingEnd ℂ) := by
  rw [← LinearMap.charpoly_toMatrix _ (Matrix.stdBasis ℂ (Fin d) (Fin d)),
    hsAdjoint_toMatrix]
  change ((LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d))
    (Matrix.stdBasis ℂ (Fin d) (Fin d)) Phi).transpose.map (starRingEnd ℂ)).charpoly = _
  rw [Matrix.charpoly_map, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]
lemma hsAdjoint_trace (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) =
      star (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Phi) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d)),
    hsAdjoint_toMatrix, Matrix.trace_conjTranspose,
    LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))]
end
section
variable {d : ℕ}
private lemma minReSpectrum_attained [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    ∃ z : ℂ, z ∈ (Phi.charpoly.roots) ∧ z.re = minReSpectrum Phi := by
  have hn := (roots_nonempty Phi).image Complex.re
  obtain ⟨z,hz,hmin⟩ := hn.csInf_mem ((roots_finite Phi).image Complex.re)
  exact ⟨z,hz,hmin⟩
private lemma hsAdjoint_roots (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    (((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi).charpoly.roots) = ((Phi.charpoly.roots)).map (starRingEnd ℂ) := by
  have hcard : Phi.charpoly.roots.card = Phi.charpoly.natDegree :=
    (IsAlgClosed.splits Phi.charpoly).natDegree_eq_card_roots.symm
  rw [ hsAdjoint_charpoly,
    ← Phi.charpoly_monic.roots_map_of_card_eq_natDegree (starRingEnd ℂ) hcard]
private lemma realParts_hsAdjoint (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    Complex.re '' {z : ℂ | z ∈ (((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi).charpoly.roots)} =
      Complex.re '' {z : ℂ | z ∈ (Phi.charpoly.roots)} := by
  rw [hsAdjoint_roots]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨w,hw,rfl⟩ := Multiset.mem_map.mp hz
    exact ⟨w,hw,by simp⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨star z, Multiset.mem_map.mpr ⟨z,hz,rfl⟩, by simp⟩
lemma extrema_hsAdjoint (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    minReSpectrum ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) = minReSpectrum Phi ∧
      maxReSpectrum ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) = maxReSpectrum Phi := by
  exact ⟨congrArg sInf (realParts_hsAdjoint Phi), congrArg sSup (realParts_hsAdjoint Phi)⟩
lemma extrema_conj (e : (Matrix (Fin d) (Fin d) ℂ) ≃ₗ[ℂ] (Matrix (Fin d) (Fin d) ℂ)) (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    minReSpectrum (e.conj Phi) = minReSpectrum Phi ∧
      maxReSpectrum (e.conj Phi) = maxReSpectrum Phi := by
  simp [minReSpectrum, maxReSpectrum, LinearEquiv.charpoly_conj]
end
section
variable {d : ℕ}
lemma faithful_fourth_roots (rho : (Matrix (Fin d) (Fin d) ℂ)) (hrho : rho.PosDef) :
    ∃ R S : (Matrix (Fin d) (Fin d) ℂ), R.IsHermitian ∧ S.IsHermitian ∧ R * S = 1 ∧ S * R = 1 ∧
      (S * S) * (S * S) = rho := by
  letI : CStarAlgebra ((Matrix (Fin d) (Fin d) ℂ)) := {}
  let W := CFC.sqrt rho
  let S := CFC.sqrt W
  let R := S⁻¹
  have hWnon : 0 ≤ W := CFC.sqrt_nonneg rho
  have hSnon : 0 ≤ S := CFC.sqrt_nonneg W
  have hWunit : IsUnit W := (CFC.isUnit_sqrt_iff rho hrho.posSemidef.nonneg).mpr hrho.isUnit
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff W hWnon).mpr hWunit
  have hHermS : S.IsHermitian := hSnon.posSemidef.isHermitian
  have hHermR : R.IsHermitian := hHermS.inv
  have hSW : S * S = W := CFC.sqrt_mul_sqrt_self W hWnon
  have hWrho : W * W = rho := CFC.sqrt_mul_sqrt_self rho hrho.posSemidef.nonneg
  refine ⟨R,S,hHermR,hHermS,?_,?_,?_⟩
  · exact Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
  · exact Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
  · rw [hSW,hWrho]
end
section
variable {d : ℕ}
private lemma unitary_conj_eq_congr (u : Matrix.unitaryGroup (Fin d) ℂ) (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) :
    LinearEquiv.conj (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u).toAlgEquiv.toLinearEquiv Phi =
      ((LinearMap.mulLeftRight ℂ ((u : (Matrix (Fin d) (Fin d) ℂ)), (u : (Matrix (Fin d) (Fin d) ℂ)).conjTranspose))).comp
        (Phi.comp ((LinearMap.mulLeftRight ℂ ((star (u : (Matrix (Fin d) (Fin d) ℂ))), (star (u : (Matrix (Fin d) (Fin d) ℂ))).conjTranspose)))) := by
  apply LinearMap.ext
  intro X
  simp only [
    LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, StarAlgEquiv.coe_toAlgEquiv,
    StarAlgEquiv.coe_symm_toAlgEquiv, Unitary.conjStarAlgAut_apply,
    Unitary.conjStarAlgAut_symm_apply, LinearMap.mulLeftRight_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  change (u : (Matrix (Fin d) (Fin d) ℂ)) * Phi ((Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) u).symm X) *
    star (u : (Matrix (Fin d) (Fin d) ℂ)) = _
  rw [Unitary.conjStarAlgAut_symm_apply]
  simp only [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
private lemma unitary_congr_trace (u : Matrix.unitaryGroup (Fin d) ℂ) (X : (Matrix (Fin d) (Fin d) ℂ)) :
    ((LinearMap.mulLeftRight ℂ ((u : (Matrix (Fin d) (Fin d) ℂ)), (u : (Matrix (Fin d) (Fin d) ℂ)).conjTranspose)) X).trace = X.trace := by
  change ((u : (Matrix (Fin d) (Fin d) ℂ)) * X * star (u : (Matrix (Fin d) (Fin d) ℂ))).trace = X.trace
  calc
    ((u : (Matrix (Fin d) (Fin d) ℂ)) * X * star (u : (Matrix (Fin d) (Fin d) ℂ))).trace = (X * (star (u : (Matrix (Fin d) (Fin d) ℂ)) * u)).trace := by
      simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle X (star (u : (Matrix (Fin d) (Fin d) ℂ))) (u : (Matrix (Fin d) (Fin d) ℂ))).symm
    _ = X.trace := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]
private lemma transition_diagonal_eigen {d : ℕ} (Φ : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (x : Fin d → ℝ) (lam : ℝ)
    (he : Φ (Matrix.diagonal (fun i => (x i : ℂ))) =
      (lam : ℂ) • Matrix.diagonal (fun i => (x i : ℂ))) :
    Matrix.mulVec (fun i j => (Φ (Matrix.single j j 1) i i).re) x = lam • x := by
  have hexpand : Matrix.diagonal (fun i => (x i : ℂ)) =
      ∑ i : Fin d, (x i : ℂ) • Matrix.single i i 1 := by
    simp [Matrix.smul_single, Matrix.sum_single_eq_diagonal]
  ext i
  have hi := congrArg (fun M : (Matrix (Fin d) (Fin d) ℂ) => (M i i).re) he
  rw [hexpand, map_sum] at hi
  simp only [map_smul] at hi
  simp_rw [Matrix.sum_apply] at hi
  simp only [Matrix.smul_apply] at hi
  have hdiag :
      ((∑ k : Fin d, (x k : ℂ) • Matrix.single k k (1 : ℂ)) i i).re = x i := by
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Finset.sum_eq_single]
  have hdiagC :
      (∑ k : Fin d, (x k : ℂ) • Matrix.single k k (1 : ℂ)) i i = (x i : ℂ) := by
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Finset.sum_eq_single]
  have hright :
      ((lam : ℂ) • ((∑ k : Fin d, (x k : ℂ) • Matrix.single k k (1 : ℂ)) i i)).re =
        lam * x i := by
    rw [hdiagC]
    simp
  rw [hright] at hi
  simpa [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Complex.mul_re, mul_comm] using hi
private lemma real_eigen_trace_bound [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (htp : (∀ X, Matrix.trace (Phi X) = Matrix.trace X))
    (lam : ℝ) (hlam : Module.End.HasEigenvalue Phi (lam : ℂ)) :
    ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi)).re ≤ (d : ℝ) * lam + (d : ℝ)^2 - d := by
  obtain ⟨Y,hY⟩ := hlam.exists_hasEigenvector
  obtain ⟨X,hX,hX0,hEX⟩ :=
    hermitian_eigen_of_star_preserving Phi lam
      (twoPositive_star_preserving Phi h2) hY.2 hY.apply_eq_smul
  let u := hX.eigenvectorUnitary
  let F := LinearEquiv.conj (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) (star u)).toAlgEquiv.toLinearEquiv Phi
  have hF2 : (KPositive 2 _ F) := by
    dsimp only [F]
    rw [unitary_conj_eq_congr]
    exact twoPositive_comp _ _ (congrMap_twoPositive _)
      (twoPositive_comp _ _ h2 (congrMap_twoPositive _))
  have hFtp : (∀ X, Matrix.trace (F X) = Matrix.trace X) := by
    intro Z
    dsimp only [F]
    rw [unitary_conj_eq_congr, LinearMap.comp_apply, LinearMap.comp_apply,
      unitary_congr_trace, htp]
    have hs : star (↑(star u) : (Matrix (Fin d) (Fin d) ℂ)) = (u : (Matrix (Fin d) (Fin d) ℂ)) := by simp
    rw [hs]
    exact unitary_congr_trace u Z
  let x := hX.eigenvalues
  have hFE : F (Matrix.diagonal (fun i => (x i : ℂ))) =
      (lam : ℂ) • Matrix.diagonal (fun i => (x i : ℂ)) :=
    hermitian_diagonal_eigen Phi X lam hX hEX
  have hx0 : x ≠ 0 := by
    intro hx
    apply hX0
    have he := hX.conjStarAlgAut_star_eigenvectorUnitary
    change (Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) (star u)) X =
      Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) at he
    have hzero : Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) = 0 := by
      change Matrix.diagonal (fun i => (x i : ℂ)) = 0
      rw [hx]
      simp
    rw [hzero] at he
    have hinv := congrArg (Unitary.conjStarAlgAut ℂ ((Matrix (Fin d) (Fin d) ℂ)) (star u)).symm he
    simpa only [StarAlgEquiv.symm_apply_apply, map_zero] using hinv
  let T := (transition F).map Complex.re
  have hT : T ∈ Matrix.colStochastic ℝ (Fin d) :=
    transition_colStochastic F
      (positive_diag_of_two F hF2)
      (fun Z => hFtp Z)
  have hTx : T *ᵥ x = lam • x := transition_diagonal_eigen F x lam hFE
  let v : Fin d → ℂ := fun i => (x i : ℂ)
  have hv0 : v ≠ 0 := by
    intro hv
    apply hx0
    funext i
    exact Complex.ofReal_injective (congrFun hv i)
  have hTv : (T.map (algebraMap ℝ ℂ)) *ᵥ v = (lam : ℂ) • v := by
    ext i
    have hi := congrArg (fun z : Fin d → ℝ => (z i : ℂ)) hTx
    simpa [Matrix.mulVec, dotProduct, v] using hi
  have hroot : (lam : ℂ) ∈ (T.map (algebraMap ℝ ℂ)).charpoly.roots := by
    apply (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mp
    rw [← Matrix.spectrum_toLin']
    exact Module.End.HasEigenvalue.mem_spectrum
      (Module.End.hasEigenvalue_of_hasEigenvector (x := v)
        ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv0⟩)
  have htrace : (LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) F).re ≤ (d : ℝ) * T.trace :=
    transition_trace_bound F hF2
  have hb := real_eigen_case_from_transition F T lam htrace hT hroot
  have htF : LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) F = LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) Phi :=
    LinearMap.trace_conj' Phi _
  simpa [realEigenBound, htF] using hb
end
section
variable {d : ℕ}
private lemma weightedAdjoint_supertrace (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (W V : Matrix (Fin d) (Fin d) ℂ) (hVW : V * W = 1) :
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (weightedAdjoint Phi W V) =
      LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) ((@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi) := by
  let CW : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) := LinearMap.mulLeftRight ℂ (W, W.conjTranspose)
  let CV : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) := LinearMap.mulLeftRight ℂ (V, V.conjTranspose)
  let F : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) := (@LinearMap.adjoint ℂ (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin d) (Fin d) ℂ) _ (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) (Matrix.frobeniusNormedAddCommGroup (m := Fin d) (n := Fin d) (α := ℂ)) hsInner hsInner (by exact FiniteDimensional.finiteDimensional_pi' ℂ _) (by exact FiniteDimensional.finiteDimensional_pi' ℂ _)) Phi
  have hCVW : CV.comp CW = LinearMap.id := by
    ext X i j
    exact congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (congr_inverse_apply V W X hVW)
  change LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (CW.comp (F.comp CV)) = LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) F
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hCVW, LinearMap.comp_id]
private lemma theorem1_faithful [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (htp : (∀ X, Matrix.trace (Phi X) = Matrix.trace X))
    (rho : (Matrix (Fin d) (Fin d) ℂ)) (hrho : rho.PosDef) (hfixed : Phi rho = rho) :
    SourceTheorem1Bound Phi := by
  obtain ⟨R,S,hR,hS,hRS,hSR,hSquare⟩ := faithful_fourth_roots rho hrho
  let W := S * S
  let V := R * R
  have hW : W.IsHermitian := by change (S * S).conjTranspose = S * S; rw [Matrix.conjTranspose_mul,hS.eq]
  have hV : V.IsHermitian := by change (R * R).conjTranspose = R * R; rw [Matrix.conjTranspose_mul,hR.eq]
  have hWV : W * V = 1 := by
    change (S * S) * (R * R) = 1
    calc
      (S * S) * (R * R) = S * (S * R) * R := by noncomm_ring
      _ = 1 := by rw [hSR,Matrix.mul_one,hSR]
  have hVW : V * W = 1 := by
    change (R * R) * (S * S) = 1
    calc
      (R * R) * (S * S) = R * (R * S) * S := by noncomm_ring
      _ = 1 := by rw [hRS,Matrix.mul_one,hRS]
  have hWA2 : (KPositive 2 _ (weightedAdjoint Phi W V)) :=
    weightedAdjoint_twoPositive Phi h2 W V
  have hWAtp : (∀ X, Matrix.trace ((weightedAdjoint Phi W V) X) = Matrix.trace X) :=
    weightedAdjoint_tracePreserving Phi W V rho hW hV hVW hSquare hfixed
  let Avg := weightedSymmetricPart Phi W V
  have hAvg2 : (KPositive 2 _ Avg) := by
    have hsum := twoPositive_add Phi (weightedAdjoint Phi W V) h2 hWA2
    have hhalf := twoPositive_smul (Phi + weightedAdjoint Phi W V) hsum
      (1 / 2) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have hh : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hh] at hhalf
    exact hhalf
  have hAvgtp : (∀ X, Matrix.trace (Avg X) = Matrix.trace X) := by
    intro X
    change ((1 / 2 : ℂ) • (Phi X + weightedAdjoint Phi W V X)).trace = X.trace
    rw [Matrix.trace_smul,Matrix.trace_add,htp X,hWAtp X]
    change (1 / 2 : ℂ) * (X.trace + X.trace) = X.trace
    ring
  have hWATrace : LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (weightedAdjoint Phi W V) = star (LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi) :=
    (weightedAdjoint_supertrace Phi W V hVW).trans (hsAdjoint_trace Phi)
  have hAvgTrace : ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Avg)).re = ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi)).re := by
    change ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) ((1 / 2 : ℂ) • (Phi + weightedAdjoint Phi W V)))).re = _
    have ht : (LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) ((1 / 2 : ℂ) • (Phi + weightedAdjoint Phi W V))) =
        (1 / 2 : ℂ) * ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi) + star ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi))) := by
      simp only [map_smul,map_add]
      rw [show LinearMap.trace ℂ ((Matrix (Fin d) (Fin d) ℂ)) (weightedAdjoint Phi W V) = star ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) Phi)) from hWATrace]
      rfl
    rw [ht]
    simp [Complex.mul_re]
    <;> ring
  obtain ⟨r,hr,hb⟩ := weighted_bendixson Phi R S hR hS hRS hSR
  have hReal := real_eigen_trace_bound Avg hAvg2 hAvgtp r hr
  obtain ⟨z,hz,hmin⟩ := minReSpectrum_attained Phi
  have hrle : r ≤ minReSpectrum Phi := by
    rw [← hmin]
    exact hb z ((root_mem_iff Phi z).mp hz)
  rw [hAvgTrace] at hReal
  dsimp [SourceTheorem1Bound]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]
end
section
variable {d : ℕ}
private def depolarized (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)) (ε : ℝ) : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  ((1-ε : ℝ) : ℂ) • Phi + ((ε / d : ℝ) : ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))
private lemma depolarized_twoPositive [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (ε : ℝ) (hε : 0 ≤ ε) (hle : ε ≤ 1) :
    (KPositive 2 _ (depolarized Phi ε)) := by
  exact twoPositive_add _ _ (twoPositive_smul _ h2 (1-ε) (by linarith))
    (twoPositive_smul _ traceIdentity_twoPositive (ε/d) (by positivity))
private lemma depolarized_tracePreserving [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (htp : (∀ X, Matrix.trace (Phi X) = Matrix.trace X)) (ε : ℝ) :
    (∀ X, Matrix.trace ((depolarized Phi ε) X) = Matrix.trace X) := by
  intro X
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [depolarized,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.smulRight_apply,Matrix.traceLinearMap_apply,LinearMap.coe_mk,AddHom.coe_mk,Matrix.trace_add,Matrix.trace_smul,
    Matrix.trace_one,Fintype.card_fin,htp X,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_natCast]
  field_simp
  <;> ring
private lemma depolarized_strict [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ 1) :
    ∀ X : (Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → X ≠ 0 → (depolarized Phi ε X).PosDef := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  exact regularization_strictly_improving _
    (twoPositive_smul Phi h2 (1-ε) (by linarith)) (ε/d) (div_pos hε hd)
private lemma depolarized_faithful_fixed [NeZero d] (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    (h2 : (KPositive 2 _ Phi)) (htp : (∀ X, Matrix.trace (Phi X) = Matrix.trace X))
    (ε : ℝ) (hε : 0 < ε) (hle : ε ≤ 1) :
    ∃ rho : (Matrix (Fin d) (Fin d) ℂ), rho.PosDef ∧ depolarized Phi ε rho = rho := by
  let T := depolarized Phi ε
  have hT2 := depolarized_twoPositive Phi h2 ε hε.le hle
  obtain ⟨rho,hPos,hTr,hFix⟩ := reuse_channel_fixed_state T
    (twoPositive_positive T hT2) (depolarized_tracePreserving Phi htp ε)
  exact ⟨rho,faithful_of_strict_fixed T (depolarized_strict Phi h2 ε hε hle)
    rho hPos hTr hFix,hFix⟩
private lemma depolarized_tendsto {α : Type*} {l : Filter α} (Phi : (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ))
    {ε : α → ℝ} (hε : Tendsto ε l (nhds 0)) :
    Tendsto (fun x => (depolarized Phi (ε x)).toContinuousLinearMap) l
      (nhds Phi.toContinuousLinearMap) := by
  have h1 : Tendsto (fun x => ((1-ε x : ℝ) : ℂ)) l (nhds 1) := by
    have hr : Tendsto (fun x => (1:ℝ)-ε x) l (nhds (1:ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub hε
    simpa only [Complex.ofReal_one] using hr.ofReal
  have h2 : Tendsto (fun x => ((ε x / d : ℝ) : ℂ)) l (nhds 0) := by
    simpa only [zero_div,Complex.ofReal_zero] using (hε.div_const (d : ℝ)).ofReal
  have h := (h1.smul_const Phi.toContinuousLinearMap).add
    (h2.smul_const (((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))).toContinuousLinearMap)
  have heq : (fun x => (depolarized Phi (ε x)).toContinuousLinearMap) =
      (fun x => ((1-ε x : ℝ) : ℂ) • Phi.toContinuousLinearMap +
        ((ε x / d : ℝ) : ℂ) • (((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))).toContinuousLinearMap) := by
    funext x
    apply ContinuousLinearMap.ext
    intro X
    rfl
  rw [heq]
  have hz : (0:ℂ) • (((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ))).toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext
    intro X
    change (0:ℂ) • ((Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Matrix (Fin d) (Fin d) ℂ)) X = 0
    exact zero_smul ℂ _
  simpa only [one_smul,hz,add_zero] using h
end
section
variable {d : ℕ}
theorem real_limit_preserves_bound {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : ∀ t, 0 < t → f t ≤ g t)
    (hf : Tendsto f atTop (nhds a))
    (hg : Tendsto g atTop (nhds b)) : a ≤ b := by
  have hdiff : Tendsto (fun t => f t - g t) atTop (nhds (a - b)) := hf.sub hg
  have hle : ∀ᶠ t : ℝ in atTop, f t - g t ≤ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact sub_nonpos.mpr (hfg t ht)
  have hzero : a - b ≤ 0 := le_of_tendsto hdiff hle
  linarith
theorem real_limit_preserves_bound_within {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), f t ≤ g t)
    (hf : Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds a))
    (hg : Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds b)) : a ≤ b := by
  have hdiff : Tendsto (fun t => f t - g t) (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (a - b)) := hf.sub hg
  have hzero : a - b ≤ 0 := le_of_tendsto hdiff (hfg.mono (fun t ht => sub_nonpos.mpr ht))
  linarith
end
section
variable {d : ℕ}
lemma theorem1_general : SourceTheorem1Goal := by
  intro d hd Phi h2 htp
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have hbound : ∀ t : ℝ, 0 < t →
      ((LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (depolarized Phi ((t+1)⁻¹)))).re ≤
        (d : ℝ) * minReSpectrum (depolarized Phi ((t+1)⁻¹)) + ((d : ℝ)^2 - d) := by
    intro t ht
    have hp : 0 < (t+1)⁻¹ := inv_pos.mpr (by linarith)
    have hle : (t+1)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by linarith)]; linarith
    obtain ⟨rho,hrho,hfix⟩ := depolarized_faithful_fixed Phi h2 htp _ hp hle
    exact theorem1_faithful _ (depolarized_twoPositive Phi h2 _ hp.le hle)
      (depolarized_tracePreserving Phi htp _) rho hrho hfix
  have heps : Tendsto (fun t : ℝ => (t+1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hconv' := depolarized_tendsto Phi heps
  have hs' := extrema_tendsto hconv'
  have ht' := (superTrace_continuous.tendsto Phi.toContinuousLinearMap).comp hconv'
  exact real_limit_preserves_bound hbound ((Complex.continuous_re.tendsto _).comp ht')
    ((hs'.1.const_mul (d : ℝ)).add_const ((d : ℝ)^2-d))
end
end D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
