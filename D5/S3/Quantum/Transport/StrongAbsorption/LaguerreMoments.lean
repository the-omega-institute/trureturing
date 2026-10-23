/- GID: D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Laguerre scaling. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.cumulant_expansion_of_moments
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17044
deltaSq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaPoly_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.continuous_deltaSq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq_pos, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.measurable_laguerreWeight, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_tilt, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly, D5.S3.Quantum.Transport.StrongAbsorption.Density.joint_delta_factor, D5.S3.Quantum.Transport.StrongAbsorption.Density.rawWeight_factor, D5.S3.Quantum.Transport.StrongAbsorption.Density.jointDeltaPoly_eval, D5.S3.Quantum.Transport.StrongAbsorption.Density.weight_cutoff_factor, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_indicator, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_tail_bound
deltaDegree: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaDegree_zero, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaDegree_succ, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaDegree_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta
deltaPoly: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaPoly_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp, D5.S3.Quantum.Transport.StrongAbsorption.Density.jointDeltaPoly, D5.S3.Quantum.Transport.StrongAbsorption.Density.jointDeltaPoly_eval
squareDeriv: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_X, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_difference, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_total, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly
eulerDeriv: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_X, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_total, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
expJet: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.exp_jet_recurrence, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correction_jet_recurrence, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.RescaledMomentExpansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
correctionJet: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correction_jet_recurrence, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.RescaledMomentExpansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
laguerreWeight: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.measurable_laguerreWeight, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_tilt, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.tilted_partition, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreMoment, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeightedMeasure, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_mgf_derivative, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_mgf, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_z_mgf, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_tilted_p2, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight, D5.S3.Quantum.Transport.StrongAbsorption.Density.weight_cutoff_factor, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_indicator, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_mass, D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityIntegral_zero, D5.S3.Quantum.Transport.StrongAbsorption.Density.weight_scaled_cutoff, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreZPower_integrable, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative
polyIntegral: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_add, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_monomial, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_nsmul, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_sum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_monomial, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_sq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp
partition: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.tilted_partition, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreMoment, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeightedMeasure, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_mgf_derivative, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_mgf, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_z_mgf, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_mass, D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_add, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.law_remainder_bigO, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.variable_observable_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion
laguerreMoment: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p2, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_tilted_p2, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection
laguerreWeightedMeasure: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_mgf_derivative, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated
laguerreH: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_near, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_near, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreH_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
laguerreHw: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_near, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
scaling_degree: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
exp_sum_prod_single: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polynomial_exp_integrable_single, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_monomial
derivation_product_eigen: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta
pair_sum: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval
derivation_sum_apply: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_total, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_total
exp_deriv_near: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.exp_jet_recurrence, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correction_deriv_near, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near
deltaDegree_zero: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaDegree_eq
deltaDegree_succ: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaDegree_eq
orthant_measure: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta
polynomial_exp_integrable_single: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_add, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_sum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable
deltaPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_powerSum, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerrePolynomial_integrable, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_delta, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly, D5.S3.Quantum.Transport.StrongAbsorption.Density.jointDeltaPoly_eval
continuous_deltaSq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.measurable_laguerreWeight, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos
deltaSq_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_tail_bound
deltaSq_pos: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos
squareDeriv_X: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_difference, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_total
eulerDeriv_X: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_total, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta
exp_jet_recurrence: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments
correction_deriv_near: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.correction_jet_recurrence
gammaCGF_analytic: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreH_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near
correctionCGF_analytic: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments
FirstOrder.congr_eventually: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.cumulant_expansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral_firstOrder, D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.variable_observable_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion
deltaDegree_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.deltaSq_scale, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.eulerDeriv_delta
laguerreWeight_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection
laguerreWeight_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_nonneg
measurable_laguerreWeight: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp
squareDeriv_difference: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta
squareDeriv_total: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly
polyIntegral_add: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_sq
polyIntegral_monomial: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_monomial
polyIntegral_nsmul: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
polyIntegral_sum: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly
polyIntegral_powerSum: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp
eulerDeriv_total: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
laguerreWeight_tilt: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.tilted_partition, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_tilted_p2
laguerrePolynomial_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreZPower_integrable, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection
singleWPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.singleWPoly_nonneg, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated
correction_jet_recurrence: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments
deltaSq_scale: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeight_scale
partition_pos: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integral, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_integrable_exp, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_mgf, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1, D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion
tilted_partition: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_mgf
squareDeriv_delta: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.squareDeriv_delta_eval
polyIntegral_X_monomial: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X
eulerDeriv_delta: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
polyIntegral_delta: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
singleWPoly_nonneg: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated
laguerreWeight_scale: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_scale
polyIntegral_X: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.polyIntegral_X_sq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_poly
squareDeriv_delta_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly
laguerreWeighted_integral: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_mgf_derivative, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq
laguerreWeighted_integrable_exp: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreWeighted_mgf_derivative
cumulant_expansion_of_moments: proof_shape: content; escape_witness: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.cumulant_expansion_of_moments; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments
partition_scale: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1_mgf
polyIntegral_X_sq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp_poly
laguerre_p1_poly: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p1
laguerreWeighted_mgf_derivative: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_iterated
laguerre_p1_mgf: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_z_mgf
laguerre_ibp_poly: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_ibp
laguerre_p1: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p2, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection
laguerre_z_mgf: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_eq
laguerre_ibp: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_p2
laguerre_p2: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerre_tilted_p2
laguerreH_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_near, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq, D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_near
laguerre_tilted_p2: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_eq
laguerreH_near: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreH_iterated, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreH_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near
laguerreH_iterated: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
laguerreHw_eq: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.laguerreHw_near
laguerreHw_near: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreHw_analytic, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.modelCorrection_near
Escape audit for public helper statements unfinished: https://github.com/the-omega-institute/trureturing/issues/19485
-/

import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import Mathlib.Topology.Algebra.MvPolynomial

namespace D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations
open MeasureTheory ProbabilityTheory Set Real Finset Filter Asymptotics MvPolynomial
open scoped Topology

noncomputable def deltaSq (M : ℕ) (x : Fin M → ℝ) : ℝ :=
  ∏ i, ∏ j, if i < j then (x i-x j)^2 else 1

private def deltaDegree (M : ℕ) : ℕ := ∑ i : Fin M, ∑ j : Fin M, if i < j then 2 else 0

private theorem scaling_degree (M : ℕ) : M + M*(M-1) = M^2 := by
  cases M with
  | zero => norm_num
  | succ k => simp; ring

private theorem exp_sum_prod_single (M : ℕ) (a : ℝ) (x : Fin M → ℝ) :
    Real.exp (-a * ∑ i, x i) = ∏ i, Real.exp (-(a*x i)) := by
  simpa using exp_sum_prod M a (x, fun _ => 0)

noncomputable def deltaPoly (M : ℕ) : MvPolynomial (Fin M) ℝ :=
  ∏ i, ∏ j, if i < j then (MvPolynomial.X i-MvPolynomial.X j)^2 else 1

private noncomputable def squareDeriv (M : ℕ) : Derivation ℝ (MvPolynomial (Fin M) ℝ) (MvPolynomial (Fin M) ℝ) :=
  MvPolynomial.mkDerivation ℝ fun i => (MvPolynomial.X i)^2

theorem derivation_product_eigen {M : ℕ} {σ : Type*} [DecidableEq σ]
    (D : Derivation ℝ (MvPolynomial (Fin M) ℝ) (MvPolynomial (Fin M) ℝ))
    (s : Finset σ) (f g : σ → MvPolynomial (Fin M) ℝ)
    (h : ∀ i ∈ s, D (f i) = g i * f i) :
    D (∏ i ∈ s, f i) = (∑ i ∈ s, g i) * ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, D.leibniz,
      h i (Finset.mem_insert_self i s), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    simp only [smul_eq_mul]
    ring

private theorem pair_sum (M : ℕ) (v : Fin M → ℝ) :
    ∑ i, ∑ j, (if i < j then v i+v j else 0) = ((M : ℝ)-1)*∑ i, v i := by
  let S := ∑ i, ∑ j, (if i < j then v i+v j else 0)
  have hswap : (∑ i, ∑ j, (if j < i then v i+v j else 0)) = S := by
    rw [Finset.sum_comm]
    simp only [S, add_comm]
  have he (i j : Fin M) :
      (if i < j then v i+v j else 0) + (if j < i then v i+v j else 0) =
        (v i+v j) - (if i = j then 2*v i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · subst j; simp; ring
    · simp [h, not_lt.mpr h.le, ne_of_gt h]
  have h2 : S+S = 2*((M : ℝ)-1)*∑ i, v i := by
    calc
      S+S = (∑ i, ∑ j, ((if i < j then v i+v j else 0)+(if j < i then v i+v j else 0))) := by
        simp only [Finset.sum_add_distrib, hswap, S]
      _ = ∑ i, ∑ j, ((v i+v j)-(if i = j then 2*v i else 0)) := by simp_rw [he]
      _ = _ := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  linarith

private theorem derivation_sum_apply {M : ℕ} {σ : Type*} (s : Finset σ)
    (D : σ → Derivation ℝ (MvPolynomial (Fin M) ℝ) (MvPolynomial (Fin M) ℝ))
    (P : MvPolynomial (Fin M) ℝ) :
    (∑ i ∈ s, D i) P = ∑ i ∈ s, D i P := by
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
    congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := ℝ)
      (A := MvPolynomial (Fin M) ℝ) (M := MvPolynomial (Fin M) ℝ)) D s) P

private noncomputable def eulerDeriv (M : ℕ) : Derivation ℝ (MvPolynomial (Fin M) ℝ) (MvPolynomial (Fin M) ℝ) :=
  MvPolynomial.mkDerivation ℝ MvPolynomial.X

noncomputable def expJet (K : ℝ → ℝ) (r : ℕ) : ℝ :=
  iteratedDeriv r (fun t => Real.exp (K t)) 0

noncomputable def correctionJet (K B : ℝ → ℝ) (r : ℕ) : ℝ :=
  iteratedDeriv r (fun t => Real.exp (K t)*B t) 0

theorem exp_deriv_near {K : ℝ → ℝ} (hK : AnalyticAt ℝ K 0) :
    deriv (fun t => Real.exp (K t)) =ᶠ[𝓝 0]
      (fun t => deriv K t*Real.exp (K t)) := by
  filter_upwards [hK.eventually_analyticAt] with t ht
  rw [ht.differentiableAt.hasDerivAt.exp.deriv]
  ring

private theorem deltaDegree_zero : deltaDegree 0 = 0 := by
  exact Nat.eq_zero_of_add_eq_zero_left rfl

private theorem deltaDegree_succ (M : ℕ) : deltaDegree (M+1) = 2*M + deltaDegree M := by
  unfold deltaDegree
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ]
  simp
  ring

noncomputable def laguerreWeight (M : ℕ) (a : ℝ) (x : Fin M → ℝ) : ℝ :=
  if ∀ i, 0 ≤ x i then Real.exp (-a*∑ i, x i) * deltaSq M x else 0

theorem orthant_measure (M : ℕ) : (volume : Measure (Fin M → ℝ)).restrict ((Set.Ici (0 : Fin M → ℝ))) = orthantMeasure M := by
  rw [← Set.pi_univ_Ici (0 : Fin M → ℝ)]
  simp only [volume_pi, Measure.restrict_pi_pi, orthantMeasure]
  rfl

theorem polynomial_exp_integrable_single {M : ℕ} {a : ℝ} (ha : 0 < a)
    (P : MvPolynomial (Fin M) ℝ) :
    Integrable (fun x => Real.exp (-a*∑ i, x i) * MvPolynomial.eval x P) (orthantMeasure M) := by
  simp_rw [exp_sum_prod_single, MvPolynomial.eval_eq', Finset.mul_sum]
  apply integrable_finsetSum
  intro d _
  have h := (Integrable.fintype_prod (fun i : Fin M => integrable_power_exp ha (d i))).const_mul (P.coeff d)
  apply h.congr
  filter_upwards [] with x
  simp only [Finset.prod_mul_distrib]
  ring

theorem deltaPoly_eval (M : ℕ) (x : Fin M → ℝ) : MvPolynomial.eval x (deltaPoly M) = deltaSq M x := by
  simp [deltaPoly, deltaSq, map_prod, apply_ite]

private theorem continuous_deltaSq (M : ℕ) : Continuous (deltaSq M) := by
  unfold deltaSq
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro j _
  split_ifs <;> fun_prop

theorem deltaSq_nonneg (M : ℕ) (x : Fin M → ℝ) : 0 ≤ deltaSq M x := by
  apply Finset.prod_nonneg
  intro i _
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · positivity
  · positivity

private theorem deltaSq_pos {M : ℕ} {x : Fin M → ℝ} (hx : Function.Injective x) : 0 < deltaSq M x := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  split_ifs with hij
  · exact sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h => (ne_of_lt hij) (hx h)))
  · exact zero_lt_one

private theorem squareDeriv_X (M : ℕ) (i : Fin M) : squareDeriv M (X i) = (X i)^2 := by
  simp [squareDeriv, MvPolynomial.mkDerivation_X]

noncomputable def polyIntegral {M : ℕ} (a : ℝ) (P : MvPolynomial (Fin M) ℝ) : ℝ :=
  ∫ x, Real.exp (-a*∑ i, x i)*MvPolynomial.eval x P ∂orthantMeasure M

private theorem eulerDeriv_X (M : ℕ) (i : Fin M) : eulerDeriv M (X i) = X i := by
  simp [eulerDeriv, MvPolynomial.mkDerivation_X]

theorem exp_jet_recurrence {K : ℝ → ℝ} (hK : AnalyticAt ℝ K 0)
    (hK0 : K 0 = 0) (n : ℕ) :
    iteratedDeriv (n+1) K 0 = expJet K (n+1)-
      ∑ i ∈ range n, (n.choose i : ℝ)*iteratedDeriv (i+1) K 0*expJet K (n-i) := by
  have h := (exp_deriv_near hK).iteratedDeriv_eq (n := n)
  rw [← iteratedDeriv_succ', iteratedDeriv_fun_mul hK.deriv.contDiffAt hK.rexp'.contDiffAt] at h
  simp_rw [← iteratedDeriv_succ'] at h
  rw [Finset.sum_range_succ] at h
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero,
    hK0, Real.exp_zero, mul_one] at h
  change expJet K (n+1) = _ at h
  dsimp only [expJet] at h ⊢
  linarith

private theorem correction_deriv_near {K B : ℝ → ℝ} (hK : AnalyticAt ℝ K 0)
    (hB : AnalyticAt ℝ B 0) :
    deriv (fun t => Real.exp (K t)*B t) =ᶠ[𝓝 0]
      (fun t => deriv K t*(Real.exp (K t)*B t)+deriv B t*Real.exp (K t)) := by
  filter_upwards [hK.eventually_analyticAt, hB.eventually_analyticAt, exp_deriv_near hK] with t ht hb he
  rw [deriv_fun_mul ht.rexp'.differentiableAt hb.differentiableAt, he]
  ring

theorem gammaCGF_analytic (d : ℝ) : AnalyticAt ℝ (gammaCGF d) 0 := by
  unfold gammaCGF
  fun_prop (disch := simp)

theorem correctionCGF_analytic (d : ℝ) : AnalyticAt ℝ (correctionCGF d) 0 := by
  unfold correctionCGF
  fun_prop (disch := simp)

theorem FirstOrder.congr_eventually {f g : ℝ → ℝ} {a b : ℝ}
    (hf : FirstOrder f a b) (hfg : f =ᶠ[atTop] g) : FirstOrder g a b := by
  exact hf.congr' (hfg.mono fun γ hγ => by dsimp only; rw [hγ]) EventuallyEq.rfl

private theorem deltaDegree_eq (M : ℕ) : deltaDegree M = M*(M-1) := by
  induction M with
  | zero => simp [deltaDegree_zero]
  | succ M h =>
    rw [deltaDegree_succ, h]
    cases M with
    | zero => norm_num
    | succ k => simp [Nat.succ_sub_one]; ring

noncomputable def partition (M : ℕ) (a : ℝ) : ℝ := ∫ x, laguerreWeight M a x

theorem laguerreWeight_integrable (M : ℕ) {a : ℝ} (ha : 0 < a) : Integrable (laguerreWeight M a) := by
  have hi := polynomial_exp_integrable_single ha (deltaPoly M)
  rw [← orthant_measure] at hi
  have he : ((Set.Ici (0 : Fin M → ℝ))).indicator (fun x => Real.exp (-a*∑ i, x i)*MvPolynomial.eval x (deltaPoly M)) = laguerreWeight M a := by
    funext x
    have hm : x ∈ (Set.Ici (0 : Fin M → ℝ)) ↔ ∀ i, 0 ≤ x i := Iff.rfl
    simp only [Set.indicator, hm, laguerreWeight, deltaPoly_eval]
  rw [← he]
  exact (integrable_indicator_iff (by measurability)).mpr hi

theorem laguerreWeight_nonneg (M : ℕ) (a : ℝ) (x : Fin M → ℝ) : 0 ≤ laguerreWeight M a x := by
  unfold laguerreWeight
  split_ifs
  · exact mul_nonneg (Real.exp_pos _).le (deltaSq_nonneg M x)
  · exact le_refl 0

private theorem measurable_laguerreWeight (M : ℕ) (a : ℝ) : Measurable (laguerreWeight M a) := by
  have hm : MeasurableSet {x : Fin M → ℝ | ∀ i, 0 ≤ x i} := measurableSet_Ici
  apply Measurable.ite hm
  · exact (by fun_prop : Measurable (fun x : Fin M → ℝ => Real.exp (-a*∑ i, x i))).mul (continuous_deltaSq M).measurable
  · exact measurable_const

private theorem squareDeriv_difference (M : ℕ) (i j : Fin M) :
    squareDeriv M ((X i-X j)^2) = 2*(X i+X j)*(X i-X j)^2 := by
  simp only [Derivation.leibniz_pow, map_sub, squareDeriv_X, nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

private theorem squareDeriv_total (M : ℕ) (P : MvPolynomial (Fin M) ℝ) :
    squareDeriv M P = ∑ i, (X i)^2 * MvPolynomial.pderiv i P := by
  have he : squareDeriv M = ∑ i : Fin M, (X i : MvPolynomial (Fin M) ℝ)^2 • MvPolynomial.pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [squareDeriv_X, derivation_sum_apply, Derivation.smul_apply, MvPolynomial.pderiv_X,
      Pi.single_apply, smul_eq_mul]
  rw [he]
  simp [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]

theorem polyIntegral_add {M : ℕ} {a : ℝ} (ha : 0 < a) (P Q : MvPolynomial (Fin M) ℝ) :
    polyIntegral a (P+Q) = polyIntegral a P + polyIntegral a Q := by
  unfold polyIntegral
  simp only [map_add, mul_add]
  exact integral_add (polynomial_exp_integrable_single ha P) (polynomial_exp_integrable_single ha Q)

private theorem polyIntegral_monomial {M : ℕ} {a : ℝ} (ha : 0 < a) (d : Fin M →₀ ℕ) (r : ℝ) :
    polyIntegral a (MvPolynomial.monomial d r) = r*∏ i, ((d i).factorial : ℝ)/a^(d i+1) := by
  unfold polyIntegral
  simp_rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    exp_sum_prod_single]
  have he : (fun x : Fin M → ℝ => (∏ i, Real.exp (-(a*x i)))*(r*∏ i, x i^d i)) =
      (fun x => r*∏ i, x i^d i*Real.exp (-(a*x i))) := by
    funext x
    rw [Finset.prod_mul_distrib]
    ring
  rw [he, integral_const_mul, orthantMeasure]
  congr 1
  change (∫ x : Fin M → ℝ, ∏ i, (fun y : ℝ => y^d i*Real.exp (-(a*y))) (x i)
    ∂Measure.pi (fun _ => (volume : Measure ℝ).restrict (Set.Ici 0))) = _
  calc
    _ = ∏ i : Fin M, ∫ y : ℝ in Set.Ici 0, y^d i*Real.exp (-(a*y)) :=
      integral_fintype_prod_eq_prod (fun i : Fin M => fun y : ℝ => y^d i*Real.exp (-(a*y)))
    _ = _ := by simp_rw [power_exp_integral ha]

private theorem polyIntegral_nsmul {M : ℕ} (a : ℝ) (n : ℕ) (P : MvPolynomial (Fin M) ℝ) :
    polyIntegral a (n • P) = (n : ℝ)*polyIntegral a P := by
  unfold polyIntegral
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  rw [show (fun x : Fin M → ℝ => Real.exp (-a*∑ i, x i)*((n : ℝ)*MvPolynomial.eval x P)) =
    (fun x => (n : ℝ)*(Real.exp (-a*∑ i, x i)*MvPolynomial.eval x P)) by funext x; ring]
  exact integral_const_mul _ _

theorem polyIntegral_sum {M : ℕ} {a : ℝ} (ha : 0 < a) {σ : Type*} (s : Finset σ)
    (P : σ → MvPolynomial (Fin M) ℝ) :
    polyIntegral a (∑ i ∈ s, P i) = ∑ i ∈ s, polyIntegral a (P i) := by
  unfold polyIntegral
  simp only [map_sum, Finset.mul_sum]
  exact integral_finsetSum s (fun i _ => by simpa only [Finset.mul_sum] using polynomial_exp_integrable_single ha (P i))

private theorem polyIntegral_powerSum (M r : ℕ) (a : ℝ) :
    polyIntegral a ((∑ i : Fin M, (X i)^r)*deltaPoly M) =
      ∫ x, (∑ i, x i^r)*laguerreWeight M a x := by
  have hs : MeasurableSet (Set.Ici (0 : Fin M → ℝ)) := measurableSet_Ici
  have he : ((Set.Ici (0 : Fin M → ℝ))).indicator (fun x : Fin M → ℝ =>
      Real.exp (-a*∑ i, x i)*MvPolynomial.eval x ((∑ i : Fin M, (X i)^r)*deltaPoly M)) =
        (fun x => (∑ i, x i^r)*laguerreWeight M a x) := by
    funext x
    have hx : x ∈ (Set.Ici (0 : Fin M → ℝ)) ↔ ∀ i, 0 ≤ x i := Iff.rfl
    simp only [Set.indicator, hx, laguerreWeight, map_mul, map_sum, map_pow, MvPolynomial.eval_X, deltaPoly_eval]
    split_ifs <;> ring
  rw [← he, integral_indicator hs, polyIntegral, ← orthant_measure]

private theorem eulerDeriv_total (M : ℕ) (P : MvPolynomial (Fin M) ℝ) :
    eulerDeriv M P = ∑ i, X i * MvPolynomial.pderiv i P := by
  have he : eulerDeriv M = ∑ i : Fin M, (X i : MvPolynomial (Fin M) ℝ) • MvPolynomial.pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [eulerDeriv_X, derivation_sum_apply, Derivation.smul_apply, MvPolynomial.pderiv_X,
      Pi.single_apply, smul_eq_mul]
  rw [he]
  simp [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]

private theorem laguerreWeight_tilt (M : ℕ) (a t : ℝ) (x : Fin M → ℝ) :
    Real.exp (t*∑ i, x i)*laguerreWeight M a x = laguerreWeight M (a-t) x := by
  unfold laguerreWeight
  split_ifs
  · rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp

theorem laguerrePolynomial_integrable {M : ℕ} {a : ℝ} (ha : 0 < a)
    (P : MvPolynomial (Fin M) ℝ) : Integrable (fun x => laguerreWeight M a x*eval x P) := by
  have h := polynomial_exp_integrable_single ha (deltaPoly M*P)
  rw [← orthant_measure] at h
  have he : (fun x : Fin M → ℝ => laguerreWeight M a x*eval x P) =
      ((Set.Ici (0 : Fin M → ℝ))).indicator (fun x => Real.exp (-a*∑ i, x i)*eval x (deltaPoly M*P)) := by
    funext x
    have hx : x ∈ (Set.Ici (0 : Fin M → ℝ)) ↔ ∀ i, 0 ≤ x i := Iff.rfl
    by_cases hp : ∀ i, 0 ≤ x i <;> simp [hx,hp,laguerreWeight,deltaPoly_eval,mul_assoc]
  rw [he]
  exact (integrable_indicator_iff (by measurability)).mpr h

theorem singleWPoly_eval (M : ℕ) (x : Fin M → ℝ) : eval x ((Finset.univ.expect (fun i : Fin M => ((X i)^2 : MvPolynomial (Fin M) ℝ)))) = (Finset.univ.expect (fun i => x i^2)) := by
  simp [Finset.expect, Algebra.smul_def,Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast,powerSum,map_sum]

theorem correction_jet_recurrence {K B : ℝ → ℝ} (hK : AnalyticAt ℝ K 0)
    (hB : AnalyticAt ℝ B 0) (hK0 : K 0 = 0) (hB0 : B 0 = 0) (n : ℕ) :
    iteratedDeriv (n+1) B 0 = correctionJet K B (n+1)-
      ∑ i ∈ range n, (n.choose i : ℝ)*
        (iteratedDeriv (i+1) K 0*correctionJet K B (n-i)+
         iteratedDeriv (i+1) B 0*expJet K (n-i)) := by
  have h := (correction_deriv_near hK hB).iteratedDeriv_eq (n := n)
  have hkD : ContDiffAt ℝ n (deriv K) 0 := hK.deriv.contDiffAt
  have hbD : ContDiffAt ℝ n (deriv B) 0 := hB.deriv.contDiffAt
  have hE : ContDiffAt ℝ n (fun t => Real.exp (K t)) 0 := hK.rexp'.contDiffAt
  have hBc : ContDiffAt ℝ n B 0 := hB.contDiffAt
  have hG : ContDiffAt ℝ n (fun t => Real.exp (K t)*B t) 0 := hE.mul hBc
  rw [← iteratedDeriv_succ', iteratedDeriv_fun_add (hkD.mul hG) (hbD.mul hE)] at h
  rw [iteratedDeriv_fun_mul hkD hG, iteratedDeriv_fun_mul hbD hE] at h
  simp_rw [← iteratedDeriv_succ'] at h
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero,
    hK0, hB0, Real.exp_zero, mul_zero, mul_one, add_zero] at h
  dsimp only [correctionJet, expJet]
  simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
  linarith

private theorem deltaSq_scale (M : ℕ) (c : ℝ) (x : Fin M → ℝ) :
    deltaSq M (fun i => c*x i) = c^(M*(M-1)) * deltaSq M x := by
  rw [← deltaDegree_eq]
  unfold deltaSq deltaDegree
  have he (i j : Fin M) :
      (if i < j then (c*x i-c*x j)^2 else (1 : ℝ)) =
        c^(if i < j then 2 else 0) * (if i < j then (x i-x j)^2 else 1) := by
    split_ifs <;> ring
  simp_rw [he, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]

theorem partition_pos (M : ℕ) {a : ℝ} (ha : 0 < a) : 0 < partition M a := by
  let U : Set (Fin M → ℝ) := (Set.univ.pi fun _ => Ioi 0) ∩ {x | 0 < deltaSq M x}
  have hopen : IsOpen U := (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)).inter
    (isOpen_lt continuous_const (continuous_deltaSq M))
  have hne : U.Nonempty := by
    refine ⟨(center M 1).1, ?_, deltaSq_pos (center_properties M zero_lt_one).2.1⟩
    simpa [Set.mem_pi] using ((strictSupportSet_membership M 1 (center M 1)).mp
      (center_properties M zero_lt_one).1).1
  have hsub : U ⊆ Function.support (laguerreWeight M a) := by
    intro x hx
    have hs : ∀ i, 0 ≤ x i := by
      have hh : ∀ i, 0 < x i := by simpa [Set.mem_pi] using hx.1
      exact fun i => (hh i).le
    change laguerreWeight M a x ≠ 0
    simp only [laguerreWeight, if_pos hs]
    exact ne_of_gt (mul_pos (Real.exp_pos _) hx.2)
  exact (integral_pos_iff_support_of_nonneg (laguerreWeight_nonneg M a)
    (laguerreWeight_integrable M ha)).mpr
    (lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono hsub))

private theorem tilted_partition (M : ℕ) (a t : ℝ) :
    (∫ x, Real.exp (t*∑ i, x i) * laguerreWeight M a x) = partition M (a-t) := by
  simp_rw [laguerreWeight_tilt]
  rfl

private theorem squareDeriv_delta (M : ℕ) :
    squareDeriv M (deltaPoly M) =
      (∑ i, ∑ j, if i < j then 2*(X i+X j) else 0) * deltaPoly M := by
  unfold deltaPoly
  apply derivation_product_eigen
  intro i _
  apply derivation_product_eigen
  intro j _
  split_ifs with h
  · exact squareDeriv_difference M i j
  · simp

private theorem polyIntegral_X_monomial {M : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin M) (d : Fin M →₀ ℕ) (r : ℝ) :
    a*polyIntegral a (X i * MvPolynomial.monomial d r) = ((d i : ℝ)+1)*polyIntegral a (MvPolynomial.monomial d r) := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, polyIntegral_monomial ha, polyIntegral_monomial ha]
  have he : (∏ j : Fin M, ((((Finsupp.single i 1 : Fin M →₀ ℕ) + d) j).factorial : ℝ)/a^(((Finsupp.single i 1 : Fin M →₀ ℕ)+d) j+1)) =
      (((d i : ℝ)+1)/a)*∏ j : Fin M, ((d j).factorial : ℝ)/a^(d j+1) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin M => ((((Finsupp.single i 1 : Fin M →₀ ℕ)+d) j).factorial : ℝ)/a^(((Finsupp.single i 1 : Fin M →₀ ℕ)+d) j+1)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j : Fin M => ((d j).factorial : ℝ)/a^(d j+1)) (Finset.mem_univ i)]
    have hp : (∏ j ∈ Finset.univ.erase i, ((((Finsupp.single i 1 : Fin M →₀ ℕ)+d) j).factorial : ℝ)/a^(((Finsupp.single i 1 : Fin M →₀ ℕ)+d) j+1)) =
        ∏ j ∈ Finset.univ.erase i, ((d j).factorial : ℝ)/a^(d j+1) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.single_apply, (Finset.mem_erase.mp hj).1, Ne.symm (Finset.mem_erase.mp hj).1]
    rw [hp]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_comm 1, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    field_simp
  rw [he]
  field_simp

noncomputable def laguerreMoment (M r : ℕ) (a : ℝ) : ℝ :=
    (∫ x, (∑ i : Fin M, x i^r)*laguerreWeight M a x)/partition M a

private theorem eulerDeriv_delta (M : ℕ) :
    eulerDeriv M (deltaPoly M) = (M*(M-1) : ℕ) • deltaPoly M := by
  have he : eulerDeriv M (deltaPoly M) =
      (∑ i : Fin M, ∑ j : Fin M, (if i < j then (2 : MvPolynomial (Fin M) ℝ) else 0))*deltaPoly M := by
    unfold deltaPoly
    apply derivation_product_eigen
    intro i _
    apply derivation_product_eigen
    intro j _
    split_ifs
    · simp only [Derivation.leibniz_pow, map_sub, eulerDeriv_X, nsmul_eq_mul, smul_eq_mul]
      norm_num <;> ring <;> simp
    · simp
  rw [← deltaDegree_eq]
  simp only [deltaDegree, nsmul_eq_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero]
  exact he

private theorem polyIntegral_delta (M : ℕ) (a : ℝ) : polyIntegral a (deltaPoly M) = partition M a := by
  have hs : MeasurableSet (Set.Ici (0 : Fin M → ℝ)) := measurableSet_Ici
  have he : ((Set.Ici (0 : Fin M → ℝ))).indicator (fun x : Fin M → ℝ =>
      Real.exp (-a*∑ i, x i)*MvPolynomial.eval x (deltaPoly M)) = laguerreWeight M a := by
    funext x
    have hx : x ∈ (Set.Ici (0 : Fin M → ℝ)) ↔ ∀ i, 0 ≤ x i := Iff.rfl
    simp only [Set.indicator, hx, laguerreWeight, deltaPoly_eval]
  rw [partition, ← he, integral_indicator hs, polyIntegral, ← orthant_measure]

noncomputable def laguerreWeightedMeasure (M : ℕ) (Q : MvPolynomial (Fin M) ℝ) : Measure (Fin M → ℝ) :=
  (ENNReal.ofReal (partition M M))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (laguerreWeight M M x*eval x Q))

theorem singleWPoly_nonneg (M : ℕ) (x : Fin M → ℝ) : 0 ≤ eval x ((Finset.univ.expect (fun i : Fin M => ((X i)^2 : MvPolynomial (Fin M) ℝ)))) := by
  rw [singleWPoly_eval]
  simp only [Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast, powerSum]
  positivity

private theorem laguerreWeight_scale (M : ℕ) {a : ℝ} (ha : 0 < a) (x : Fin M → ℝ) :
    laguerreWeight M 1 (a • x) = a^(M*(M-1)) * laguerreWeight M a x := by
  have hs : (∀ i, 0 ≤ (a • x) i) ↔ ∀ i, 0 ≤ x i := by
    simp [Pi.smul_apply, smul_eq_mul, (mul_nonneg_iff_of_pos_left ha)]
  unfold laguerreWeight
  simp only [hs]
  split_ifs with hx
  · have hd : deltaSq M (a • x) = a^(M*(M-1))*deltaSq M x := deltaSq_scale M a x
    rw [hd]
    simp only [Pi.smul_apply, smul_eq_mul, one_mul, Finset.mul_sum, neg_mul]
    ring
  · simp

private theorem polyIntegral_X {M : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin M) (P : MvPolynomial (Fin M) ℝ) :
    a*polyIntegral a (X i*P) = polyIntegral a P + polyIntegral a (X i*MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, mul_add, polyIntegral_add ha]
    linarith
  | monomial d r =>
    rw [MvPolynomial.X_mul_pderiv_monomial, polyIntegral_nsmul]
    rw [polyIntegral_X_monomial ha]
    ring

private theorem squareDeriv_delta_eval (M : ℕ) (x : Fin M → ℝ) :
    MvPolynomial.eval x (squareDeriv M (deltaPoly M)) =
      2*((M : ℝ)-1)*(∑ i, x i)*deltaSq M x := by
  rw [squareDeriv_delta, map_mul]
  have hd : MvPolynomial.eval x (deltaPoly M) = deltaSq M x := deltaPoly_eval M x
  rw [hd]
  simp only [map_sum, apply_ite, map_mul, map_ofNat, MvPolynomial.eval_X, map_add, map_zero]
  have he : (∑ i, ∑ j, (if i < j then 2*(x i+x j) else 0)) =
      2*∑ i, ∑ j, if i < j then x i+x j else 0 := by
    simp only [mul_ite, mul_zero, Finset.mul_sum]
  rw [he, pair_sum]
  ring

private theorem laguerreWeighted_integral {M : ℕ} (hM : 1 ≤ M) (Q : MvPolynomial (Fin M) ℝ)
    (hQ : ∀ x, 0 ≤ eval x Q) (f : (Fin M → ℝ) → ℝ) :
    (∫ x, f x ∂laguerreWeightedMeasure M Q) =
      (∫ x, laguerreWeight M M x*eval x Q*f x)/partition M M := by
  have hm : Measurable (fun x : Fin M → ℝ => laguerreWeight M M x*eval x Q) :=
    (measurable_laguerreWeight M M).mul (MvPolynomial.continuous_eval Q).measurable
  unfold laguerreWeightedMeasure
  rw [integral_smul_measure,ENNReal.toReal_inv,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul,ENNReal.toReal_ofReal (mul_nonneg (laguerreWeight_nonneg M M _) (hQ _))]
  have hpos : 0 < partition M M := partition_pos M (by exact_mod_cast (show 0 < M by omega))
  rw [ENNReal.toReal_ofReal hpos.le]
  ring

private theorem laguerreWeighted_integrable_exp {M : ℕ} (hM : 1 ≤ M) (Q : MvPolynomial (Fin M) ℝ)
    (hQ : ∀ x, 0 ≤ eval x Q) {t : ℝ} (ht : t < (M : ℝ)^2) :
    Integrable (fun x => Real.exp (t*(Finset.univ.expect x))) (laguerreWeightedMeasure M Q) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have ha : 0 < (M : ℝ)-t/(M : ℝ) := by rw [sub_pos,div_lt_iff₀ hm]; nlinarith
  have hmeas : Measurable (fun x : Fin M → ℝ => laguerreWeight M M x*eval x Q) :=
    (measurable_laguerreWeight M M).mul (MvPolynomial.continuous_eval Q).measurable
  have hi : Integrable (fun x => Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x*eval x Q) := by
    have he (x : Fin M → ℝ) : Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x =
        laguerreWeight M ((M : ℝ)-t/(M : ℝ)) x := by
      simp only [Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast, powerSum]
      rw [show t*((M : ℝ)⁻¹*∑ i, x i) = (t/(M : ℝ))*∑ i, x i by ring]
      exact laguerreWeight_tilt M M (t/(M : ℝ)) x
    simp_rw [he]
    exact laguerrePolynomial_integrable ha Q
  unfold laguerreWeightedMeasure
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (partition_pos M hm)))
  apply (integrable_withDensity_iff_integrable_smul' hmeas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [smul_eq_mul,ENNReal.toReal_ofReal (mul_nonneg (laguerreWeight_nonneg M M _) (hQ _)),
    mul_assoc,mul_comm,mul_left_comm] using hi

noncomputable def laguerreH (M : ℕ) : ℝ → ℝ :=
  mgf ((fun x : Fin M → ℝ => Finset.univ.expect x)) (laguerreWeightedMeasure M 1)

noncomputable def laguerreHw (M : ℕ) : ℝ → ℝ :=
  mgf ((fun x : Fin M → ℝ => Finset.univ.expect x)) (laguerreWeightedMeasure M ((Finset.univ.expect (fun i : Fin M => ((X i)^2 : MvPolynomial (Fin M) ℝ)))))

theorem cumulant_expansion_of_moments (m k : ℕ → ℝ → ℝ) (a b c d : ℕ → ℝ)
    (hm : ∀ r, FirstOrder (m r) (a r) (b r))
    (hk : ∀ γ : ℝ, 0 < γ → ∀ n : ℕ,
      k (n+1) γ = m (n+1) γ-
        ∑ i ∈ range n, (n.choose i : ℝ)*k (i+1) γ*m (n-i) γ)
    (hc : ∀ n : ℕ, c (n+1) = a (n+1)-
        ∑ i ∈ range n, (n.choose i : ℝ)*c (i+1)*a (n-i))
    (hd : ∀ n : ℕ, d (n+1) = b (n+1)-
        ∑ i ∈ range n, (n.choose i : ℝ)*(c (i+1)*b (n-i)+d (i+1)*a (n-i))) :
    ∀ r : ℕ, 1 ≤ r → FirstOrder (k r) (c r) (d r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    have hsum := FirstOrder.sum (range n)
      (fun i γ => (n.choose i : ℝ)*(k (i+1) γ*m (n-i) γ))
      (fun i => (n.choose i : ℝ)*(c (i+1)*a (n-i)))
      (fun i => (n.choose i : ℝ)*(c (i+1)*b (n-i)+d (i+1)*a (n-i)))
      (fun i hi => ((ih (i+1) (by have := Finset.mem_range.mp hi; omega) (by omega)).mul (hm (n-i))).const_mul _)
    have hh := (hm (n+1)).sub hsum
    have hca : a (n+1)-(∑ i ∈ range n, (n.choose i : ℝ)*(c (i+1)*a (n-i))) = c (n+1) := by
      simpa only [mul_assoc] using (hc n).symm
    rw [hca, ← hd n] at hh
    apply D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.FirstOrder.congr_eventually hh
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    rw [hk γ (lt_of_lt_of_le zero_lt_one hγ) n]
    simp only [mul_assoc]

private theorem partition_scale (M : ℕ) {a : ℝ} (ha : 0 < a) :
    partition M a = (a^(M^2))⁻¹ * partition M 1 := by
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Fin M → ℝ)) (laguerreWeight M 1) a (hR := ha.le)
  simp_rw [laguerreWeight_scale M ha] at h
  rw [integral_const_mul] at h
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, smul_eq_mul] at h
  change a^(M*(M-1)) * partition M a = (a^M)⁻¹ * partition M 1 at h
  have hp : a^(M^2) * partition M a = partition M 1 := by
    calc
      _ = a^M * (a^(M*(M-1)) * partition M a) := by rw [← mul_assoc, ← pow_add, scaling_degree]
      _ = a^M * ((a^M)⁻¹ * partition M 1) := congrArg (fun q => a^M*q) h
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
  calc
    _ = (a^(M^2))⁻¹ * (a^(M^2) * partition M a) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
    _ = _ := congrArg (fun q => (a^(M^2))⁻¹*q) hp

theorem polyIntegral_X_sq {M : ℕ} {a : ℝ} (ha : 0 < a) (i : Fin M) (P : MvPolynomial (Fin M) ℝ) :
    a*polyIntegral a ((X i)^2*P) = 2*polyIntegral a (X i*P) + polyIntegral a ((X i)^2*MvPolynomial.pderiv i P) := by
  have h := polyIntegral_X ha i (X i*P)
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, one_mul] at h
  have h1 : X i*(X i*P) = (X i)^2*P := by ring
  have h2 : X i*(P+X i*MvPolynomial.pderiv i P) = X i*P+(X i)^2*MvPolynomial.pderiv i P := by ring
  rw [h1, h2, polyIntegral_add ha] at h
  linarith

private theorem laguerre_p1_poly {M : ℕ} {a : ℝ} (ha : 0 < a) :
    a*polyIntegral a ((∑ i : Fin M, X i)*deltaPoly M) = (M : ℝ)^2*partition M a := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => polyIntegral_X ha i (deltaPoly M))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← polyIntegral_sum ha, ← polyIntegral_sum ha,
    ← eulerDeriv_total, eulerDeriv_delta, polyIntegral_nsmul, polyIntegral_delta] at h
  simp only [← Finset.sum_mul] at h
  have hd : (M : ℝ)+(M*(M-1) : ℕ) = (M : ℝ)^2 := by exact_mod_cast scaling_degree M
  rw [← add_mul, hd] at h
  exact h

theorem laguerreWeighted_mgf_derivative {M : ℕ} (hM : 1 ≤ M) (Q : MvPolynomial (Fin M) ℝ)
    (hQ : ∀ x, 0 ≤ eval x Q) (r : ℕ) :
    iteratedDeriv r (mgf ((fun x : Fin M → ℝ => Finset.univ.expect x)) (laguerreWeightedMeasure M Q)) 0 =
      (∫ x, laguerreWeight M M x*eval x Q*(Finset.univ.expect x)^r)/partition M M := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have hm2 : 0 < (M : ℝ)^2 := sq_pos_of_pos hm
  have hs : Set.Iio ((M : ℝ)^2) ⊆ integrableExpSet ((fun x : Fin M → ℝ => Finset.univ.expect x)) (laguerreWeightedMeasure M Q) := by
    intro t ht
    exact laguerreWeighted_integrable_exp hM Q hQ ht
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet ((fun x : Fin M → ℝ => Finset.univ.expect x)) (laguerreWeightedMeasure M Q)) :=
    (interior_mono hs) (by simpa using hm2)
  rw [iteratedDeriv_mgf_zero h0]
  exact laguerreWeighted_integral hM Q hQ _

private theorem laguerre_p1_mgf (M : ℕ) {a t : ℝ} (ha : 0 < a) (hat : t < a) :
    (∫ x, Real.exp (t*∑ i, x i) * laguerreWeight M a x) / partition M a =
      (a/(a-t))^(M^2) := by
  rw [tilted_partition, partition_scale M (sub_pos.mpr hat), partition_scale M ha]
  have hz := (partition_pos M (zero_lt_one : (0 : ℝ) < 1)).ne'
  rw [mul_div_mul_right _ _ hz, div_pow]
  field_simp

private theorem laguerre_ibp_poly {M : ℕ} {a : ℝ} (ha : 0 < a) :
    a*polyIntegral a ((∑ i : Fin M, (X i)^2)*deltaPoly M) =
      2*(M : ℝ)*polyIntegral a ((∑ i : Fin M, X i)*deltaPoly M) := by
  have he : polyIntegral a (squareDeriv M (deltaPoly M)) =
      (2*((M : ℝ)-1))*polyIntegral a ((∑ i : Fin M, X i)*deltaPoly M) := by
    unfold polyIntegral
    simp only [squareDeriv_delta_eval, map_mul, map_sum, MvPolynomial.eval_X, deltaPoly_eval]
    rw [show (fun x : Fin M → ℝ => Real.exp (-a*∑ i, x i)*(2*((M : ℝ)-1)*(∑ i, x i)*deltaSq M x)) =
      (fun x => (2*((M : ℝ)-1))*(Real.exp (-a*∑ i, x i)*((∑ i, x i)*deltaSq M x))) by funext x; ring,
      integral_const_mul]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => polyIntegral_X_sq ha i (deltaPoly M))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← polyIntegral_sum ha, ← polyIntegral_sum ha, ← polyIntegral_sum ha,
    ← squareDeriv_total] at h
  simp only [← Finset.sum_mul] at h
  linarith

theorem laguerre_p1 {M : ℕ} {a : ℝ} (ha : 0 < a) : laguerreMoment M 1 a = (M : ℝ)^2/a := by
  have h := laguerre_p1_poly (M := M) ha
  have hp1 := polyIntegral_powerSum M 1 a
  simp only [pow_one] at hp1
  rw [hp1] at h
  unfold laguerreMoment
  simp only [pow_one]
  have hp := (partition_pos M ha).ne'
  apply (div_eq_iff hp).mpr
  field_simp
  nlinarith

private theorem laguerre_z_mgf {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : t < (M : ℝ)^2) :
    (∫ x, Real.exp (t*((∑ i, x i)/(M : ℝ))) * laguerreWeight M M x) / partition M M =
      ((1-t/(M : ℝ)^2)^(M^2))⁻¹ := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have ht' : t/(M : ℝ) < M := (div_lt_iff₀ hm).mpr (by nlinarith)
  have h := laguerre_p1_mgf M hm ht'
  have he : (fun x : Fin M → ℝ => Real.exp (t*((∑ i, x i)/(M : ℝ)))*laguerreWeight M M x) =
      (fun x => Real.exp ((t/(M : ℝ))*∑ i, x i)*laguerreWeight M M x) := by
    funext x
    congr 2
    ring
  rw [he, h, ← inv_pow]
  congr 1
  field_simp

private theorem laguerre_ibp {M : ℕ} {a : ℝ} (ha : 0 < a) :
    a*laguerreMoment M 2 a = 2*(M : ℝ)*laguerreMoment M 1 a := by
  have h := laguerre_ibp_poly (M := M) ha
  rw [polyIntegral_powerSum] at h
  have hp1 := polyIntegral_powerSum M 1 a
  simp only [pow_one] at hp1
  rw [hp1] at h
  unfold laguerreMoment
  simp only [pow_one]
  rw [← mul_div_assoc, ← mul_div_assoc, h]

theorem laguerre_p2 {M : ℕ} {a : ℝ} (ha : 0 < a) : laguerreMoment M 2 a = 2*(M : ℝ)^3/a^2 := by
  have h := laguerre_ibp (M := M) ha
  rw [laguerre_p1 ha] at h
  apply (eq_div_iff (pow_ne_zero _ ha.ne')).mpr
  field_simp at h
  nlinarith

private theorem laguerreH_eq {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : t < (M : ℝ)^2) :
    laguerreH M t = Real.exp (gammaCGF ((M : ℝ)^2) t) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have hs : 0 < 1-t/(M : ℝ)^2 := by
    have h := (div_lt_one₀ (sq_pos_of_pos hm)).mpr ht
    linarith
  unfold laguerreH mgf
  rw [laguerreWeighted_integral hM 1 (by intro x; simp)]
  simp only [map_one,mul_one]
  have h := laguerre_z_mgf hM ht
  have he : (fun x : Fin M → ℝ => laguerreWeight M M x*Real.exp (t*(Finset.univ.expect x))) =
      (fun x => Real.exp (t*((∑ i, x i)/(M : ℝ)))*laguerreWeight M M x) := by
    funext x
    simp only [Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast,powerSum,pow_one]
    rw [mul_comm (laguerreWeight M M x)]
    congr 1
    congr 1
    ring
  rw [he,h]
  unfold gammaCGF
  rw [neg_mul,Real.exp_neg]
  have hc : (M : ℝ)^2 = (M^2 : ℕ) := (Nat.cast_pow M 2).symm
  have hs' : 0 < 1-t/(M^2 : ℕ) :=
    lt_of_lt_of_eq hs (congrArg (HSub.hSub 1) (congrArg (HDiv.hDiv t) hc))
  rw [hc,Real.exp_nat_mul,Real.exp_log hs']

private theorem laguerre_tilted_p2 {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : t < (M : ℝ)^2) :
    (∫ x, (Finset.univ.expect (fun i => x i^2))*Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x)/
      (∫ x, Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x) = 2*((1-t/(M : ℝ)^2)^2)⁻¹ := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have ha : 0 < (M : ℝ)-t/(M : ℝ) := by rw [sub_pos, div_lt_iff₀ hm]; nlinarith
  have hw (x : Fin M → ℝ) : Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x =
      laguerreWeight M ((M : ℝ)-t/(M : ℝ)) x := by
    simp only [Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast, powerSum]
    rw [show t*((M : ℝ)⁻¹*∑ i, x i) = (t/(M : ℝ))*∑ i, x i by ring]
    exact laguerreWeight_tilt M M (t/(M : ℝ)) x
  simp_rw [mul_assoc, hw]
  simp only [Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast, powerSum]
  have hn : (fun x : Fin M → ℝ => ((M : ℝ)⁻¹*∑ i, x i^2)*laguerreWeight M ((M : ℝ)-t/(M : ℝ)) x) =
    (fun x => (M : ℝ)⁻¹*((∑ i, x i^2)*laguerreWeight M ((M : ℝ)-t/(M : ℝ)) x)) := by funext x; ring
  rw [hn, integral_const_mul]
  rw [mul_div_assoc]
  have hmom := laguerre_p2 (M := M) ha
  simp only [laguerreMoment, partition] at hmom
  rw [hmom]
  field_simp

theorem laguerreH_near {M : ℕ} (hM : 1 ≤ M) :
    laguerreH M =ᶠ[𝓝 0] (fun t => Real.exp (gammaCGF ((M : ℝ)^2) t)) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  filter_upwards [isOpen_Iio.mem_nhds (sq_pos_of_pos hm)] with t ht
  exact laguerreH_eq hM ht

theorem laguerreH_iterated {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    (∫ x, laguerreWeight M M x*(Finset.univ.expect x)^r)/partition M M = expJet (gammaCGF ((M : ℝ)^2)) r := by
  have h := laguerreWeighted_mgf_derivative hM 1 (by intro x; simp) r
  simp only [map_one,mul_one] at h
  rw [← h]
  exact (laguerreH_near hM).iteratedDeriv_eq (n := r)

private theorem laguerreHw_eq {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : t < (M : ℝ)^2) :
    laguerreHw M t = 2*laguerreH M t*(inverseSlope ((M : ℝ)^2) t)^2 := by
  let I := ∫ x, Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x
  let J := ∫ x, (Finset.univ.expect (fun i => x i^2))*Real.exp (t*(Finset.univ.expect x))*laguerreWeight M M x
  have hH : laguerreH M t = I/partition M M := by
    unfold laguerreH mgf
    rw [laguerreWeighted_integral hM 1 (by intro x; simp)]
    simp only [map_one,mul_one,one_mul,I,mul_comm]
  have hJ : laguerreHw M t = J/partition M M := by
    unfold laguerreHw mgf
    rw [laguerreWeighted_integral hM ((Finset.univ.expect (fun i : Fin M => ((X i)^2 : MvPolynomial (Fin M) ℝ)))) (singleWPoly_nonneg M)]
    simp only [singleWPoly_eval,J,mul_comm,mul_assoc,mul_left_comm]
  have hI : I ≠ 0 := by
    intro h0
    have h := laguerreH_eq hM ht
    rw [hH,h0,zero_div] at h
    exact (Real.exp_ne_zero _ ) h.symm
  have htilt := laguerre_tilted_p2 hM ht
  change J/I = _ at htilt
  rw [hJ,hH]
  calc
    J/partition M M = (J/I)*(I/partition M M) := (div_mul_div_cancel₀ hI).symm
    _ = _ := by rw [htilt]; unfold inverseSlope; simp only [inv_pow]; ring

theorem laguerreHw_near {M : ℕ} (hM : 1 ≤ M) :
    laguerreHw M =ᶠ[𝓝 0]
      (fun t => 2*Real.exp (gammaCGF ((M : ℝ)^2) t)*(inverseSlope ((M : ℝ)^2) t)^2) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  filter_upwards [isOpen_Iio.mem_nhds (sq_pos_of_pos hm)] with t ht
  rw [laguerreHw_eq hM ht,laguerreH_eq hM ht]

end D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
