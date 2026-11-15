/- GID: D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.claim; result=D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation.result; claim=D5/S3/Analytic/SpectralGap/WeightedGapPolynomialCertificate.claim
   digest: Weighted Dirichlet spectral gap comparison. -/
/-
admission_basis: open-problem-resolution (#27107; Refuted)
proof_shape: per-declaration rows below; object definitions are not proof witnesses.
escape_witness: none
Direct frozen dependencies: declaration GID@statement_id in each row.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27756
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.trial_hasDerivAt; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_form_lower, node_form_lower, simple_node_orientation, strong_eigenfunction_weak, strong_subinterval_nonzero, strong_zero_derivative_ne_zero, strong_zero_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.trial_derivative_continuous; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: energy_linear_combination, ground_form_lower, node_form_lower, strong_eigenfunction_weak, strong_subinterval_nonzero, strong_zero_derivative_ne_zero, strong_zero_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strongEigenfunction; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eigenfunction_mass_orthogonal, first_shooting_root_is_minmax, ground_form_lower, ground_spectrum_lower, ground_spectrum_upper, minmax_upper_of_two_eigenfunctions, node_form_lower, node_spectrum_lower, nozero_spectrum_lower, second_shooting_root_is_minmax, second_spectrum_upper, shooting_regular, simple_node_orientation, strong_eigenfunction_energy, strong_eigenfunction_weak, strong_neg, strong_subinterval_nonzero, strong_zero_derivative_ne_zero, strong_zero_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.bilinearEnergy; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: bilinear_energy_symmetric, eigenfunction_mass_orthogonal, energy_linear_combination, minmax_upper_of_one_function, minmax_upper_of_two_eigenfunctions, strong_eigenfunction_energy, strong_eigenfunction_weak
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.bilinearMass; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: bilinear_mass_symmetric, eigenfunction_mass_orthogonal, mass_linear_combination, minmax_upper_of_one_function, minmax_upper_of_two_eigenfunctions, strong_eigenfunction_energy, strong_eigenfunction_weak
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.bilinear_energy_symmetric; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eigenfunction_mass_orthogonal
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.bilinear_mass_symmetric; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eigenfunction_mass_orthogonal
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_eigenfunction_weak; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: eigenfunction_mass_orthogonal, minmax_upper_of_two_eigenfunctions, strong_eigenfunction_energy
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_eigenfunction_energy; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_spectrum_upper, minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.eigenfunction_mass_orthogonal; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.trial_mass_positive; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minmax_lower_of_form, minmax_lower_of_node, minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.positive_comparison; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_comparison
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_comparison; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_form_lower, node_form_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.trial_linear_combination; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minmax_upper_of_one_function, minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.trial_derivative_linear_combination; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: energy_linear_combination
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.energy_linear_combination; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minmax_upper_of_one_function, minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.mass_linear_combination; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: minmax_upper_of_one_function, minmax_upper_of_two_eigenfunctions
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.minmax_upper_of_one_function; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_spectrum_upper
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_spectrum_upper; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: first_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.minmax_upper_of_two_eigenfunctions; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_spectrum_upper
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.second_spectrum_upper; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.minmax_lower_of_form; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_spectrum_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.minmax_lower_of_node; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: node_spectrum_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_form_lower; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: ground_spectrum_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_spectrum_lower; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: nozero_spectrum_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.node_form_lower; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: node_spectrum_lower
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.node_spectrum_lower; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.shooting_regular; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: first_shooting_root_is_minmax, second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.zero_endpoint_poincare; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: interval_poincare
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.interval_poincare; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: interval_solution_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.second_order_unique_zero; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: strong_subinterval_nonzero, strong_zero_derivative_ne_zero
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixedPotential; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: fixed_potential_bounds, fixed_potential_class, fixed_refutation_of_brackets, result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixedWeight; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: affine_q_bound, fixed_refutation_of_brackets, fixed_weight_bounds, fixed_weight_class, result, series_zero_is_shooting
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixed_potential_bounds; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: fixed_potential_class
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixed_weight_bounds; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: affine_q_bound, fixed_weight_class, result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixed_potential_class; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: fixed_refutation_of_brackets
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixed_weight_class; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: fixed_refutation_of_brackets
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.bracket_gap_negative; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: fixed_refutation_of_brackets
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.fixed_refutation_of_brackets; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.series_zero_is_shooting; proof_shape: content; escape_witness: none; Direct frozen dependencies: none; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_0; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_0
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_1; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_0
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_2; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_1
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_3; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_1
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_4; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_2
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_5; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_2
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_6; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_3
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.endpoint_7; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: root_3
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.determinant_zero_between; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: root_0, root_1, root_2, root_3
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.root_0; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.root_1; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.root_2; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.root_3; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.interval_solution_separation; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: strong_zero_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.no_first_interior_zero; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: first_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.at_most_one_interior_zero; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_subinterval_nonzero; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: strong_zero_separation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_zero_separation; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: first_shooting_root_is_minmax, second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.continuous_nonzero_orientation; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: nozero_spectrum_lower, simple_node_orientation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_neg; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: nozero_spectrum_lower, simple_node_orientation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.strong_zero_derivative_ne_zero; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.impossible_positive_sides; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: simple_node_orientation
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.simple_node_orientation; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.nozero_spectrum_lower; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: first_shooting_root_is_minmax, second_shooting_root_is_minmax
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.first_shooting_root_is_minmax; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.second_shooting_root_is_minmax; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.affine_q_bound; proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: result
D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.result; proof_shape: content; escape_witness: none; Direct frozen dependencies: D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr@sha256:7740d0d639e691784931b94a9f39a1e729a89943b3d162fba0338723c2634562, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.add@sha256:5de53c0c21af00283b7122bf98d3837ef8ead8e83fc76566c9470310e38b6b50, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.const@sha256:883830ed15e01b32856f92ae231290e494d5fd04397feef656ceb5c5a7c99beb, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.input@sha256:7c1ff706fd917d42fd8bac14c6f0823e57eb66d7d31e76616f7baea58a3ea428, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.mul@sha256:b961a54e1cd3f732396a35f036a1063ecddf913e56610486ab178f76030fbd77, D5/S0/Certificates/BoxCover/RationalIntervalExpression.Expr.neg@sha256:885ae424fe49611ff9ecd91cc5ed0fa3fc0a91f5f14c6f0d43681fde0f796826, D5/S0/Certificates/BoxCover/RationalIntervalExpression.bounds@sha256:80b990090589e41d7b17dd2c077f625c7948ccee7ea79be2582db82bd0911139, D5/S0/Certificates/BoxCover/RationalIntervalExpression.check@sha256:c8ae7c793983ac85ff158ba276ee97b9df81d50768609863072c6b2d348ddbc1, D5/S0/Certificates/BoxCover/RationalIntervalExpression.checked_expression_encloses@sha256:55fd549ad21c17edd29bfbda30075f70836c1b8c2023a9cc913348680e05632f, D5/S0/Certificates/BoxCover/RationalIntervalExpression.value@sha256:563dbc7e0fc0596db696c2b1a71aa49ec288d39d8cf201638560baef6cca7f55, D5/S3/Analytic/MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap@sha256:0cf5d494d7644aacf3153094db2ceff3a3ea55ea0862ea00c498585a6e9677ea; consumers: none (settling result)
-/
import D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate
import D5.S3.Analytic.MomentOrthogonalPrimitiveGap
import D5.S3.Analytic.SpectralGap.WeightedGapMajorant
import D5.S3.Analytic.SpectralGap.WeightedGapStateSeries
import D5.S3.Analytic.SpectralGap.WeightedGapDeterminant
import D5.S3.Analytic.SpectralGap.WeightedGapVolterra
import Mathlib.Analysis.ODE.Gronwall
open Set MeasureTheory
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open scoped BigOperators
open D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate D5.S3.Analytic.SpectralGap.WeightedGapMajorant D5.S3.Analytic.SpectralGap.WeightedGapStateSeries D5.S3.Analytic.SpectralGap.WeightedGapDeterminant D5.S3.Analytic.SpectralGap.WeightedGapVolterra
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
namespace D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation
private theorem trial_hasDerivAt {u : ℝ → ℝ} (hu : dirichletTrial u) {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) : HasDerivAt u (derivWithin u interval x) x := by
  exact (hu.1.differentiableOn_one x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
private theorem trial_derivative_continuous {u : ℝ → ℝ} (hu : dirichletTrial u) : ContinuousOn (derivWithin u interval) interval := by
  exact hu.1.continuousOn_derivWithin (uniqueDiffOn_Icc Real.pi_pos) le_rfl
private def strongEigenfunction (V w : ℝ → ℝ) (z : ℝ) (u : ℝ → ℝ) : Prop :=
  dirichletTrial u ∧ ∀ x ∈ Ioo 0 Real.pi, HasDerivAt (derivWithin u interval) ((V x-z*w x)*u x) x
private noncomputable def bilinearEnergy (V u v : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..Real.pi, derivWithin u interval x * derivWithin v interval x + V x * u x * v x
private noncomputable def bilinearMass (w u v : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..Real.pi, w x * u x * v x
private theorem bilinear_energy_symmetric (V u v : ℝ → ℝ) : bilinearEnergy V u v = bilinearEnergy V v u := by
  unfold bilinearEnergy; congr 1; funext x; ring
private theorem bilinear_mass_symmetric (w u v : ℝ → ℝ) : bilinearMass w u v = bilinearMass w v u := by
  unfold bilinearMass; congr 1; funext x; ring
private theorem strong_eigenfunction_weak {V w u v : ℝ → ℝ} {z : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hv : dirichletTrial v) : bilinearEnergy V u v = z * bilinearMass w u v := by
  have hdu := trial_derivative_continuous hu.1
  have hdv := trial_derivative_continuous hv
  have hcontu := hu.1.1.continuousOn
  have hcontv := hv.1.continuousOn
  have hforce := (hV.sub (hw.const_mul z)).mul hcontu
  have hbd0 : v 0 = 0 := hv.2 0 (by simp)
  have hbdpi : v Real.pi = 0 := hv.2 Real.pi (by simp)
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt (u := derivWithin u interval) (u' := fun x => (V x-z*w x)*u x) (v := v) (v' := derivWithin v interval) (by simpa [interval, uIcc_of_le Real.pi_pos.le] using hdu) (by simpa [interval, uIcc_of_le Real.pi_pos.le] using hcontv) (by simpa [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] using hu.2) (by simpa [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] using (fun x hx => trial_hasDerivAt hv hx)) (hforce.intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le) (hdv.intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le)
  simp only [hbd0, hbdpi, mul_zero, sub_self] at hparts
  have hdm := (hdu.mul hdv).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hvm := ((hV.mul hcontu).mul hcontv).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hwm := ((hw.mul hcontu).mul hcontv).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hEint : IntervalIntegrable (fun x => derivWithin u interval x * derivWithin v interval x + V x*u x*v x) volume 0 Real.pi := hdm.add hvm
  have hWMint : IntervalIntegrable (fun x => z*(w x*u x*v x)) volume 0 Real.pi :=
    hwm.const_mul z
  have heq : (∫ x in (0:ℝ)..Real.pi, ((V x-z*w x)*u x)*v x + derivWithin u interval x * derivWithin v interval x) = bilinearEnergy V u v - z * bilinearMass w u v := by
    unfold bilinearEnergy bilinearMass; rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hEint hWMint]; congr 1; funext x; ring
  rw [heq] at hparts; linarith
private theorem strong_eigenfunction_energy {V w u : ℝ → ℝ} {z : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) : energy V u = z * weightedMass w u := by
  have h := strong_eigenfunction_weak hV hw hu hu.1
  simpa [bilinearEnergy, bilinearMass, energy, weightedMass, pow_two, mul_assoc] using h
private theorem eigenfunction_mass_orthogonal {V w u v : ℝ → ℝ} {z y : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hv : strongEigenfunction V w y v) (hzy : z ≠ y) : bilinearMass w u v = 0 := by
  have h1 := strong_eigenfunction_weak hV hw hu hv.1
  have h2 := strong_eigenfunction_weak hV hw hv hu.1
  rw [bilinear_energy_symmetric V v u, bilinear_mass_symmetric w v u] at h2
  have hp : (z-y) * bilinearMass w u v = 0 := by nlinarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hzy)
private theorem trial_mass_positive {w u : ℝ → ℝ} (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hu : dirichletTrial u) (hne : u ≠ 0) : 0 < weightedMass w u := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hne
  have hxi : x ∈ Ioo 0 Real.pi := by
    by_contra hh
    exact hx (hu.2 x hh)
  have hxc : x ∈ interval := Ioo_subset_Icc_self hxi
  have hm := hw.mul (hu.1.continuousOn.pow 2)
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt Real.pi_pos (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℝ)) interval) hm (fun y hy => mul_nonneg (hwp y ⟨hy.1.le,hy.2⟩).le (sq_nonneg _)) ⟨x,hxc,mul_pos (hwp x hxc) (sq_pos_of_ne_zero hx)⟩
  simpa only [weightedMass, intervalIntegral.integral_zero, Pi.mul_apply, Pi.pow_apply] using h
private theorem positive_comparison (a b : ℝ) (hab : a ≤ b) (f df g dg q : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b)) (hg : ContinuousOn g (Icc a b)) (hdg : ContinuousOn dg (Icc a b)) (hq : ContinuousOn q (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < g x) (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (dg x) x) (hdgd : ∀ x ∈ Ioo a b, HasDerivAt dg (q x*g x) x) (hfa : f a = 0) (hfb : f b = 0) : 0 ≤ ∫ x in a..b, df x^2 + q x*f x^2 := by
  let R := fun x => dg x / g x
  have hR : ContinuousOn R (Icc a b) :=
    hdg.div hg (fun x hx => (hpos x hx).ne')
  have hRd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt R (q x - R x^2) x := by
    have hne := (hpos x ⟨hx.1.le, hx.2.le⟩).ne'
    convert (hdgd x hx).div (hgd x hx) hne using 1
    dsimp [R]
    field_simp <;> ring
  let F := fun x => f x^2 * R x
  let dF := fun x => 2*f x*df x*R x + f x^2*(q x-R x^2)
  have hcF : ContinuousOn F (Icc a b) := (hf.pow 2).mul hR
  have hcdF : ContinuousOn dF (Icc a b) := by
    exact (((hf.const_mul 2).mul hdf).mul hR).add ((hf.pow 2).mul (hq.sub (hR.pow 2)))
  have hdF (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt F (dF x) x := by
    convert ((hfd x hx).pow 2).mul (hRd x hx) using 1 <;> dsimp [F, dF] <;> ring
  have hiF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcF hdF (hcdF.intervalIntegrable_of_Icc (μ := volume) hab)
  have hiFzero : (∫ x in a..b, dF x) = 0 := by
    simpa [F, hfa, hfb] using hiF
  have hs : ContinuousOn (fun x => (df x-R x*f x)^2) (Icc a b) :=
    (hdf.sub (hR.mul hf)).pow 2
  have hi : (∫ x in a..b, df x^2 + q x*f x^2) = (∫ x in a..b, (df x-R x*f x)^2) + ∫ x in a..b, dF x := by
    rw [← intervalIntegral.integral_add (hs.intervalIntegrable_of_Icc (μ := volume) hab) (hcdF.intervalIntegrable_of_Icc (μ := volume) hab)]
    congr 1; funext x; dsimp [dF]; ring
  rw [hi, hiFzero, add_zero]; exact intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
private theorem ground_comparison (a b : ℝ) (hab : a < b) (f df u du q : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b)) (hu : ContinuousOn u (Icc a b)) (hdu : ContinuousOn du (Icc a b)) (hq : ContinuousOn q (Icc a b)) (hun : ∀ x ∈ Icc a b, 0 ≤ u x) (hup : ∀ x ∈ Ioo a b, 0 < u x) (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) (hud : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x) (hdud : ∀ x ∈ Ioo a b, HasDerivAt du (q x*u x) x) (hfa : f a = 0) (hfb : f b = 0) : 0 ≤ ∫ x in a..b, df x^2 + q x*f x^2 := by
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let Q := fun n x => q x*u x/(u x+ε n)
  let F := fun n x => df x^2+Q n x*f x^2
  have hden (n : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : 0 < u x+ε n :=
    add_pos_of_nonneg_of_pos (hun x hx) (hε n)
  have hQc (n : ℕ) : ContinuousOn (Q n) (Icc a b) :=
    (hq.mul hu).div (hu.add continuousOn_const) (fun x hx => (hden n x hx).ne')
  have hFc (n : ℕ) : ContinuousOn (F n) (Icc a b) :=
    (hdf.pow 2).add ((hQc n).mul (hf.pow 2))
  have hn (n : ℕ) : 0 ≤ ∫ x in a..b, F n x := by
    apply positive_comparison a b hab.le f df (fun x => u x+ε n) du (Q n) hf hdf (hu.add continuousOn_const) hdu (hQc n) (hden n) hfd (fun x hx => (hud x hx).add_const (ε n)) _ hfa hfb; intro x hx
    convert hdud x hx using 1
    dsimp [Q]; exact div_mul_cancel₀ _ (hden n x ⟨hx.1.le,hx.2.le⟩).ne'
  have hQabs (n : ℕ) (x : ℝ) (hx : x ∈ Icc a b) : |Q n x| ≤ |q x| := by
    have hratio : 0 ≤ u x/(u x+ε n) ∧ u x/(u x+ε n) ≤ 1 := by
      constructor
      · exact div_nonneg (hun x hx) (hden n x hx).le
      · apply (div_le_one (hden n x hx)).2
        linarith [hε n]
    calc
      |Q n x| = |q x| * (u x/(u x+ε n)) := by
        dsimp [Q]; rw [mul_div_assoc, abs_mul, abs_of_nonneg hratio.1]
      _ ≤ |q x| * 1 := mul_le_mul_of_nonneg_left hratio.2 (abs_nonneg _)
      _ = _ := mul_one _
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := a) (b := b) (l := Filter.atTop) (F := F) (f := fun x => df x^2+q x*f x^2) (fun x => df x^2+|q x| * f x^2) (Filter.Eventually.of_forall (fun n => by
      simpa only [uIoc_of_le hab.le] using ((hFc n).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc))
    (Filter.Eventually.of_forall (fun n => ae_of_all _ (fun x hx => by
      rw [uIoc_of_le hab.le] at hx
      have hc : x ∈ Icc a b := Ioc_subset_Icc_self hx
      rw [Real.norm_eq_abs]
      calc
        |F n x| ≤ |df x^2|+|Q n x*f x^2| := abs_add_le _ _
        _ ≤ df x^2+|q x| * f x^2 := by
          rw [abs_of_nonneg (sq_nonneg (df x)), abs_mul, abs_of_nonneg (sq_nonneg (f x))]
          have hh := mul_le_mul_of_nonneg_right (hQabs n x hc) (sq_nonneg (f x))
          linarith only [hh])))
    (((hdf.pow 2).add (hq.abs.mul (hf.pow 2))).intervalIntegrable_of_Icc (μ := volume) hab.le)
    (ae_of_all _ (fun x hx => by
      rw [uIoc_of_le hab.le] at hx
      by_cases hxb : x=b
      · subst x
        simpa [F,hfb] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => df b^2) Filter.atTop (nhds (df b^2)))
      · have hxint : x ∈ Ioo a b := ⟨hx.1,lt_of_le_of_ne hx.2 hxb⟩
        have hp := hup x hxint
        have heps : Filter.Tendsto ε Filter.atTop (nhds (0:ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hquot := (tendsto_const_nhds (x := q x*u x)).div ((tendsto_const_nhds (x := u x)).add heps) (by simpa using hp.ne')
        have hh := (tendsto_const_nhds (x := df x^2)).add (hquot.mul (tendsto_const_nhds (x := f x^2)))
        simpa [F,Q,add_zero,mul_div_cancel_right₀ _ hp.ne'] using hh))
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hn)
private theorem trial_linear_combination {u v : ℝ → ℝ} (hu : dirichletTrial u) (hv : dirichletTrial v) (a b : ℝ) : dirichletTrial (fun x => a*u x+b*v x) := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using (ContDiffOn.const_smul a hu.1).add (ContDiffOn.const_smul b hv.1)
  · intro x hx
    simp [hu.2 x hx,hv.2 x hx]
private theorem trial_derivative_linear_combination {u v : ℝ → ℝ} (hu : dirichletTrial u) (hv : dirichletTrial v) (a b : ℝ) (x : ℝ) (hx : x ∈ interval) : derivWithin (fun y => a*u y+b*v y) interval x = a*derivWithin u interval x+b*derivWithin v interval x := by
  have hud := (hu.1.differentiableOn_one x hx).hasDerivWithinAt
  have hvd := (hv.1.differentiableOn_one x hx).hasDerivWithinAt
  exact ((hud.const_mul a).add (hvd.const_mul b)).derivWithin
    (uniqueDiffOn_Icc Real.pi_pos x hx)
private theorem energy_linear_combination {V u v : ℝ → ℝ} (hV : ContinuousOn V interval) (hu : dirichletTrial u) (hv : dirichletTrial v) (a b : ℝ) : energy V (fun x => a*u x+b*v x) = a^2*energy V u+ 2*a*b*bilinearEnergy V u v+b^2*energy V v := by
  have hcu := hu.1.continuousOn
  have hcv := hv.1.continuousOn
  have hdu := trial_derivative_continuous hu
  have hdv := trial_derivative_continuous hv
  have hiu : IntervalIntegrable (fun x => derivWithin u interval x^2+V x*u x^2) volume 0 Real.pi :=
    ((hdu.pow 2).add (hV.mul (hcu.pow 2))).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hiv : IntervalIntegrable (fun x => derivWithin v interval x^2+V x*v x^2) volume 0 Real.pi :=
    ((hdv.pow 2).add (hV.mul (hcv.pow 2))).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hic : IntervalIntegrable (fun x => derivWithin u interval x*derivWithin v interval x+V x*u x*v x) volume 0 Real.pi :=
    ((hdu.mul hdv).add ((hV.mul hcu).mul hcv)).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  unfold energy bilinearEnergy; rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hiu.const_mul (a^2)) (hic.const_mul (2*a*b)), ← intervalIntegral.integral_add ((hiu.const_mul (a^2)).add (hic.const_mul (2*a*b))) (hiv.const_mul (b^2))]; apply intervalIntegral.integral_congr; intro x hx; rw [uIcc_of_le Real.pi_pos.le] at hx; dsimp only; rw [trial_derivative_linear_combination hu hv a b x hx]; ring
private theorem mass_linear_combination {w u v : ℝ → ℝ} (hw : ContinuousOn w interval) (hu : dirichletTrial u) (hv : dirichletTrial v) (a b : ℝ) : weightedMass w (fun x => a*u x+b*v x) = a^2*weightedMass w u+ 2*a*b*bilinearMass w u v+b^2*weightedMass w v := by
  have hcu := hu.1.continuousOn
  have hcv := hv.1.continuousOn
  have hiu : IntervalIntegrable (fun x => w x*u x^2) volume 0 Real.pi :=
    (hw.mul (hcu.pow 2)).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hiv : IntervalIntegrable (fun x => w x*v x^2) volume 0 Real.pi :=
    (hw.mul (hcv.pow 2)).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hic : IntervalIntegrable (fun x => w x*u x*v x) volume 0 Real.pi :=
    ((hw.mul hcu).mul hcv).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  unfold weightedMass bilinearMass; rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hiu.const_mul (a^2)) (hic.const_mul (2*a*b)), ← intervalIntegral.integral_add ((hiu.const_mul (a^2)).add (hic.const_mul (2*a*b))) (hiv.const_mul (b^2))]; congr 1; funext x; ring
private theorem minmax_upper_of_one_function {V w u : ℝ → ℝ} {z : ℝ} (hu : dirichletTrial u) (hne : u ≠ 0) (he : energy V u ≤ z*weightedMass w u) (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) : z ∈ minmaxUpperBounds V w 1 := by
  let L := Submodule.span ℝ {u}
  refine ⟨L,inferInstance,finrank_span_singleton hne,?_,?_⟩
  · intro f hf
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hf
    change dirichletTrial (fun x => a*u x); simpa only [zero_mul,add_zero] using trial_linear_combination hu hu a 0
  · intro f hf
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hf
    have hE := energy_linear_combination hV hu hu a 0
    have hM := mass_linear_combination hw hu hu a 0
    simp only [mul_zero,zero_mul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0)] at hE hM; change energy V (fun x => a*u x) ≤ z*weightedMass w (fun x => a*u x); rw [hE,hM]; nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr he)]
private theorem ground_spectrum_upper {V w u : ℝ → ℝ} {z : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hne : u ≠ 0) (he : isSpectrum V w e) : e 0 ≤ z := by
  apply (he.2.2.2 0).2.2.1; exact minmax_upper_of_one_function hu.1 hne (strong_eigenfunction_energy hV hw hu).le hV hw
private theorem minmax_upper_of_two_eigenfunctions {V w u v : ℝ → ℝ} {z y : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hu : strongEigenfunction V w z u) (hv : strongEigenfunction V w y v) (hune : u ≠ 0) (hvne : v ≠ 0) (hzy : z < y) : y ∈ minmaxUpperBounds V w 2 := by
  have hMu := trial_mass_positive hw hwp hu.1 hune
  have hMv := trial_mass_positive hw hwp hv.1 hvne
  have hortho := eigenfunction_mass_orthogonal hV hw hu hv hzy.ne
  have hEu := strong_eigenfunction_energy hV hw hu
  have hEv := strong_eigenfunction_energy hV hw hv
  have hEuv := strong_eigenfunction_weak hV hw hu hv.1
  rw [hortho,mul_zero] at hEuv
  let F : (ℝ × ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun p x => p.1*u x+p.2*v x
      map_add' := by intro p q; funext x; dsimp; ring
      map_smul' := by intro a p; funext x; dsimp; ring }
  have hFzero (p : ℝ × ℝ) (hp : F p = 0) : p=0 := by
    have hh := mass_linear_combination hw hu.1 hv.1 p.1 p.2
    change weightedMass w (F p) = _ at hh; rw [hp,hortho] at hh
    have hMzero : weightedMass w (0 : ℝ → ℝ)=0 := by simp [weightedMass]
    rw [hMzero] at hh; simp only [mul_zero,zero_mul,add_zero] at hh
    have hp1 : p.1=0 := by
      by_contra hp1
      have hpos := mul_pos (sq_pos_of_ne_zero hp1) hMu
      nlinarith [mul_nonneg (sq_nonneg p.2) hMv.le]
    have hp2 : p.2=0 := by
      by_contra hp2
      have hpos := mul_pos (sq_pos_of_ne_zero hp2) hMv
      nlinarith [mul_nonneg (sq_nonneg p.1) hMu.le]
    exact Prod.ext hp1 hp2
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).mpr hFzero
  refine ⟨LinearMap.range F,inferInstance,?_,?_,?_⟩
  · simpa using LinearMap.finrank_range_of_inj hinj
  · intro f hf
    obtain ⟨p,rfl⟩ := hf
    exact trial_linear_combination hu.1 hv.1 p.1 p.2
  · intro f hf
    obtain ⟨p,rfl⟩ := hf
    change energy V (fun x => p.1*u x+p.2*v x) ≤ y*weightedMass w (fun x => p.1*u x+p.2*v x); rw [energy_linear_combination hV hu.1 hv.1, mass_linear_combination hw hu.1 hv.1,hEu,hEv,hEuv,hortho]
    have hh : 0 ≤ p.1^2*(y-z)*weightedMass w u := by positivity
    nlinarith
private theorem second_spectrum_upper {V w u v : ℝ → ℝ} {z y : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hu : strongEigenfunction V w z u) (hv : strongEigenfunction V w y v) (hune : u ≠ 0) (hvne : v ≠ 0) (hzy : z < y) (he : isSpectrum V w e) : e 1 ≤ y := by
  apply (he.2.2.2 1).2.2.1; exact minmax_upper_of_two_eigenfunctions hV hw hwp hu hv hune hvne hzy
private theorem minmax_lower_of_form {V w : ℝ → ℝ} {z : ℝ} {n : ℕ} (hn : 0 < n) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hlower : ∀ u, dirichletTrial u → z*weightedMass w u ≤ energy V u) {r : ℝ} (hr : r ∈ minmaxUpperBounds V w n) : z ≤ r := by
  obtain ⟨L,hfin,hdim,htrial,hupper⟩ := hr
  letI := hfin
  obtain ⟨u,hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := L)).mp (by simpa only [hdim] using hn)
  have hune : (u : ℝ → ℝ) ≠ 0 := by
    intro h; apply hu; exact Subtype.ext h
  have hmass := trial_mass_positive hw hwp (htrial u u.property) hune
  have hlo := hlower u (htrial u u.property)
  have hhi := hupper u u.property
  nlinarith
private theorem minmax_lower_of_node {V w : ℝ → ℝ} {z ξ : ℝ} (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hlower : ∀ u, dirichletTrial u → u ξ = 0 → z*weightedMass w u ≤ energy V u) {r : ℝ} (hr : r ∈ minmaxUpperBounds V w 2) : z ≤ r := by
  obtain ⟨L,hfin,hdim,htrial,hupper⟩ := hr
  letI := hfin
  let ev : L →ₗ[ℝ] ℝ :=
    { toFun := fun u => (u:ℝ→ℝ) ξ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hdimlt : Module.finrank ℝ ℝ < Module.finrank ℝ L := by simp [hdim]
  have hk : LinearMap.ker ev ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdimlt
  obtain ⟨u,hu,hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hvalne : (u:ℝ→ℝ) ≠ 0 := by intro h; exact hune (Subtype.ext h)
  have hnode : (u:ℝ→ℝ) ξ = 0 := hu
  have hmass := trial_mass_positive hw hwp (htrial u u.property) hvalne
  have hlo := hlower u (htrial u u.property) hnode
  have hhi := hupper u u.property
  nlinarith
private theorem ground_form_lower {V w u : ℝ → ℝ} {z : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hup : ∀ x ∈ Ioo 0 Real.pi, 0 < u x) (f : ℝ → ℝ) (hf : dirichletTrial f) : z*weightedMass w f ≤ energy V f := by
  have hcu := hu.1.1.continuousOn
  have hdu := trial_derivative_continuous hu.1
  have hdf := trial_derivative_continuous hf
  have hq := hV.sub (hw.const_mul z)
  have hun : ∀ x ∈ Icc 0 Real.pi, 0 ≤ u x := by
    intro x hx
    by_cases hx0 : x=0
    · subst x; rw [hu.1.2 0 (by simp)]
    by_cases hxpi : x=Real.pi
    · subst x; rw [hu.1.2 Real.pi (by simp)]
    exact (hup x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hxpi⟩).le
  have hpos := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_comparison 0 Real.pi Real.pi_pos f (derivWithin f interval) u (derivWithin u interval) (fun x => V x-z*w x) hf.1.continuousOn hdf hcu hdu hq hun hup (fun x hx => trial_hasDerivAt hf hx) (fun x hx => trial_hasDerivAt hu.1 hx) hu.2 (hf.2 0 (by simp)) (hf.2 Real.pi (by simp))
  have hE : IntervalIntegrable (fun x => derivWithin f interval x^2+V x*f x^2) volume 0 Real.pi :=
    ((hdf.pow 2).add (hV.mul (hf.1.continuousOn.pow 2))).intervalIntegrable_of_Icc (μ := volume)
    Real.pi_pos.le
  have hM : IntervalIntegrable (fun x => w x*f x^2) volume 0 Real.pi :=
    (hw.mul (hf.1.continuousOn.pow 2)).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have heq : energy V f - z*weightedMass w f = ∫ x in (0:ℝ)..Real.pi, derivWithin f interval x^2 + (V x-z*w x)*f x^2 := by
    unfold energy weightedMass; rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hE (hM.const_mul z)]; congr 1; funext x; ring
  rw [← heq] at hpos; linarith
private theorem ground_spectrum_lower {V w u : ℝ → ℝ} {z : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hu : strongEigenfunction V w z u) (hup : ∀ x ∈ Ioo 0 Real.pi, 0 < u x) (he : isSpectrum V w e) : z ≤ e 0 := by
  apply (he.2.2.2 0).2.2.2; intro r hr; exact minmax_lower_of_form (by norm_num : 0<1) hw hwp (ground_form_lower hV hw hu hup) hr
private theorem node_form_lower {V w u : ℝ → ℝ} {z ξ : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hξ : ξ ∈ Ioo 0 Real.pi) (huξ : u ξ = 0) (hl : ∀ x ∈ Ioo 0 ξ, 0 < u x) (hr : ∀ x ∈ Ioo ξ Real.pi, u x < 0) (f : ℝ → ℝ) (hf : dirichletTrial f) (hfξ : f ξ = 0) : z*weightedMass w f ≤ energy V f := by
  let q := fun x => V x-z*w x
  let R := fun x => derivWithin f interval x^2+q x*f x^2
  have hq : ContinuousOn q interval := hV.sub (hw.const_mul z)
  have hdu := trial_derivative_continuous hu.1
  have hdf := trial_derivative_continuous hf
  have hcR : ContinuousOn R interval :=
    (hdf.pow 2).add (hq.mul (hf.1.continuousOn.pow 2))
  have hL : Icc 0 ξ ⊆ interval := Icc_subset_Icc le_rfl hξ.2.le
  have hR : Icc ξ Real.pi ⊆ interval := Icc_subset_Icc hξ.1.le le_rfl
  have hln : ∀ x ∈ Icc 0 ξ, 0 ≤ u x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he|he
    · subst x; rw [hu.1.2 0 (by simp)]
    rcases eq_or_lt_of_le hx.2 with ht|ht
    · subst x; rw [huξ]
    exact (hl x ⟨he,ht⟩).le
  have hrn : ∀ x ∈ Icc ξ Real.pi, 0 ≤ -u x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he|he
    · subst x; rw [huξ]; simp
    rcases eq_or_lt_of_le hx.2 with ht|ht
    · subst x; rw [hu.1.2 Real.pi (by simp)]; simp
    exact neg_nonneg.mpr (hr x ⟨he,ht⟩).le
  have hleft := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_comparison 0 ξ hξ.1 f (derivWithin f interval) u (derivWithin u interval) q (hf.1.continuousOn.mono hL) (hdf.mono hL) (hu.1.1.continuousOn.mono hL) (hdu.mono hL) (hq.mono hL) hln hl (fun x hx => trial_hasDerivAt hf ⟨hx.1,hx.2.trans hξ.2⟩) (fun x hx => trial_hasDerivAt hu.1 ⟨hx.1,hx.2.trans hξ.2⟩) (fun x hx => hu.2 x ⟨hx.1,hx.2.trans hξ.2⟩) (hf.2 0 (by simp)) hfξ
  have hright := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.ground_comparison ξ Real.pi hξ.2 f (derivWithin f interval) (fun x => -u x) (fun x => -derivWithin u interval x) q (hf.1.continuousOn.mono hR) (hdf.mono hR) (hu.1.1.continuousOn.neg.mono hR) (hdu.neg.mono hR) (hq.mono hR) hrn (fun x hx => neg_pos.mpr (hr x hx)) (fun x hx => trial_hasDerivAt hf ⟨hξ.1.trans hx.1,hx.2⟩) (fun x hx => (trial_hasDerivAt hu.1 ⟨hξ.1.trans hx.1,hx.2⟩).neg) (fun x hx => by
      convert (hu.2 x ⟨hξ.1.trans hx.1,hx.2⟩).neg using 1 <;>
        first | rfl | simp only [q,Pi.neg_apply,mul_neg])
    hfξ (hf.2 Real.pi (by simp))
  have hadd := intervalIntegral.integral_add_adjacent_intervals ((hcR.mono hL).intervalIntegrable_of_Icc (μ := volume) hξ.1.le) ((hcR.mono hR).intervalIntegrable_of_Icc (μ := volume) hξ.2.le)
  have hE : IntervalIntegrable (fun x => derivWithin f interval x^2+V x*f x^2) volume 0 Real.pi :=
    ((hdf.pow 2).add (hV.mul (hf.1.continuousOn.pow 2))).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have hM : IntervalIntegrable (fun x => w x*f x^2) volume 0 Real.pi :=
    (hw.mul (hf.1.continuousOn.pow 2)).intervalIntegrable_of_Icc (μ := volume) Real.pi_pos.le
  have heq : energy V f-z*weightedMass w f = ∫ x in (0:ℝ)..Real.pi, R x := by
    unfold energy weightedMass; rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hE (hM.const_mul z)]; congr 1; funext x; dsimp [R,q]; ring
  rw [← sub_nonneg,heq,← hadd]; exact add_nonneg hleft hright
private theorem node_spectrum_lower {V w u : ℝ → ℝ} {z ξ : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0 < w x) (hu : strongEigenfunction V w z u) (hξ : ξ ∈ Ioo 0 Real.pi) (huξ : u ξ = 0) (hl : ∀ x ∈ Ioo 0 ξ, 0 < u x) (hr : ∀ x ∈ Ioo ξ Real.pi, u x < 0) (he : isSpectrum V w e) : z ≤ e 1 := by
  apply (he.2.2.2 1).2.2.2; intro r hr'; exact minmax_lower_of_node hw hwp (node_form_lower hV hw hu hξ huξ hl hr) hr'
private theorem shooting_regular {V w : ℝ → ℝ} {z : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hz : isShootingEigenvalue V w z) : ∃ u : ℝ → ℝ, strongEigenfunction V w z u ∧ u ≠ 0 ∧ derivWithin u interval 0 = 1 := by
  classical
  obtain ⟨v,hv,hint,hv0,hvpi,hvol⟩ := hz
  let Q := fun x => (V x-z*w x)*v x
  have hQ : ContinuousOn Q interval := (hV.sub (hw.const_mul z)).mul hv
  let q := fun x => Q (projIcc 0 Real.pi Real.pi_pos.le x)
  have hq : Continuous q := hQ.domRestrict.comp continuous_projIcc
  have hqe (x : ℝ) (hx : x ∈ interval) : q x = Q x := by
    simp [q,projIcc_of_mem Real.pi_pos.le hx]
  let P := fun x => ∫ t in (0:ℝ)..x, q t
  let S := fun x => ∫ t in (0:ℝ)..x, t*q t
  let U := fun x => x+x*P x-S x
  let dU := fun x => 1+P x
  have hPd (x : ℝ) : HasDerivAt P (q x) x := hq.integral_hasStrictDerivAt 0 x |>.hasDerivAt
  have hSd (x : ℝ) : HasDerivAt S (x*q x) x :=
    (continuous_id.mul hq).integral_hasStrictDerivAt 0 x |>.hasDerivAt
  have hUd (x : ℝ) : HasDerivAt U (dU x) x := by
    convert ((hasDerivAt_id x).add ((hasDerivAt_id x).mul (hPd x))).sub (hSd x) using 1 <;> first | rfl | (dsimp only [dU,id]; ring)
  have hdUc : Continuous dU := continuous_const.add (continuous_iff_continuousAt.mpr (fun x => (hPd x).continuousAt))
  have hUc : ContDiff ℝ 1 U := by
    rw [contDiff_one_iff_deriv]; exact ⟨fun x => (hUd x).differentiableAt, hdUc.congr (fun x => (hUd x).deriv.symm)⟩
  have hUe (x : ℝ) (hx : x ∈ interval) : U x = v x := by
    rw [hvol x hx]; dsimp [U,P,S]
    have hi1 : IntervalIntegrable (fun t => x*q t) volume 0 x := (hq.intervalIntegrable 0 x).const_mul x
    have hi2 : IntervalIntegrable (fun t => t*q t) volume 0 x := (continuous_id.mul hq).intervalIntegrable 0 x
    rw [← intervalIntegral.integral_const_mul, add_sub_assoc, ← intervalIntegral.integral_sub hi1 hi2]; congr 1; apply intervalIntegral.integral_congr; intro t ht; dsimp only; rw [uIcc_of_le hx.1] at ht; rw [hqe t ⟨ht.1,ht.2.trans hx.2⟩]; dsimp [Q]; ring
  let u := fun x => if x ∈ interval then U x else 0
  have hue (x : ℝ) (hx : x ∈ interval) : u x = U x := if_pos hx
  have hut : dirichletTrial u := by
    refine ⟨hUc.contDiffOn.congr (fun x hx => hue x hx),?_⟩
    intro x hx
    by_cases hxc : x ∈ interval
    · have he : x=0 ∨ x=Real.pi := by
        rcases eq_or_lt_of_le hxc.1 with he|hlt
        · exact Or.inl he.symm
        · exact Or.inr (le_antisymm hxc.2 (le_of_not_gt (fun hh => hx ⟨hlt,hh⟩)))
      rcases he with rfl|rfl
      · rw [hue 0 hxc,hUe 0 hxc,hv0]
      · rw [hue Real.pi hxc,hUe Real.pi hxc,hvpi]
    · exact if_neg hxc
  have hdu (x : ℝ) (hx : x ∈ interval) : derivWithin u interval x = dU x := by
    apply HasDerivWithinAt.derivWithin _ (uniqueDiffOn_Icc Real.pi_pos x hx); exact (hUd x).hasDerivWithinAt.congr (fun y hy => hue y hy) (hue x hx)
  refine ⟨u,⟨hut,?_⟩,?_,?_⟩
  · intro x hx
    have hevent : derivWithin u interval =ᶠ[nhds x] dU := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      exact hdu y hy
    have hdd := (hasDerivAt_const x (1:ℝ)).add (hPd x)
    have hqxu : q x = (V x-z*w x)*u x := by
      rw [hqe x ⟨hx.1.le,hx.2.le⟩,hue x ⟨hx.1.le,hx.2.le⟩,hUe x ⟨hx.1.le,hx.2.le⟩]
    simpa only [zero_add,hqxu] using hdd.congr_of_eventuallyEq hevent
  · intro hzero
    have h := hdu 0 ⟨le_rfl,Real.pi_pos.le⟩
    simp [hzero,dU,P] at h
  · rw [hdu 0 ⟨le_rfl,Real.pi_pos.le⟩]
    simp [dU,P]
private theorem zero_endpoint_poincare (D : ℝ) (hD : 0 < D) (f df : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 D)) (hdf : ContinuousOn df (Icc 0 D)) (hd : ∀ x ∈ Ioo 0 D, HasDerivAt f (df x) x) (hf0 : f 0=0) (hfD : f D=0) : (∫ x in (0:ℝ)..D, f x^2) ≤ D^2/8*(∫ x in (0:ℝ)..D, df x^2) := by
  have hint := hdf.intervalIntegrable_of_Icc (μ := volume) hD.le
  have hprim (x : ℝ) (hx : x ∈ Icc (0:ℝ) D) : (∫ t in (0:ℝ)..x, df t)=f x := by
    have hsub : Icc (0:ℝ) x ⊆ Icc 0 D := Icc_subset_Icc le_rfl hx.2
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hf.mono hsub) (fun y hy => hd y ⟨hy.1,hy.2.trans_le hx.2⟩) ((hdf.mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1)
    simpa [hf0] using hh
  have hc : ContinuousOn (fun x => (df x:ℂ)) (Icc 0 D) :=
    Complex.continuous_ofReal.comp_continuousOn hdf
  have hmem : MemLp (fun x => (df x:ℂ)) 2 (volume.restrict (Icc 0 D)) := by
    apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable measurableSet_Icc)).mpr; exact (hc.norm.pow 2).integrableOn_Icc
  have hm : ∀ r : ℕ, r<1 → ∫ x in Icc (0:ℝ) D, (x:ℂ)^r*(df x:ℂ)=0 := by
    intro r hr
    have hr0 : r=0 := by omega
    subst r
    simp only [pow_zero,one_mul]; rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hD.le, intervalIntegral.integral_ofReal,hprim D ⟨hD.le,le_rfl⟩,hfD]
    rfl
  have h := D5.S3.Analytic.MomentOrthogonalPrimitiveGap.complex_L2_moment_primitive_gap D hD 1 (by omega) (fun x => (df x:ℂ)) hmem hm
  have heq : (∫ x in Icc (0:ℝ) D, ‖∫ t in (0:ℝ)..x, (df t:ℂ)‖^2) = ∫ x in (0:ℝ)..D, f x^2 := by
    rw [intervalIntegral.integral_of_le hD.le,← integral_Icc_eq_integral_Ioc]; apply setIntegral_congr_fun measurableSet_Icc; intro x hx; dsimp only; rw [intervalIntegral.integral_ofReal,hprim x hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [heq] at h
  norm_num only [Nat.cast_one,mul_one,show (1:ℝ)+1=2 by norm_num,show (4:ℝ)*2=8 by norm_num] at h
  simpa only [
    Complex.norm_real,Real.norm_eq_abs,sq_abs,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hD.le] using h
private theorem interval_poincare (a b : ℝ) (hab : a < b) (f df : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) (hfa : f a=0) (hfb : f b=0) : (∫ x in a..b, f x^2) ≤ (b-a)^2/8*(∫ x in a..b, df x^2) := by
  have hm : MapsTo (fun x => a+x) (Icc (0:ℝ) (b-a)) (Icc a b) := by
    simpa only [id_eq, add_zero, add_sub_cancel] using
      ((monotone_const : Monotone (fun _ : ℝ => a)).add monotone_id).mapsTo_Icc
        (a := 0) (b := b-a)
  have h := zero_endpoint_poincare (b-a) (sub_pos.mpr hab) (fun x => f (a+x)) (fun x => df (a+x)) (hf.comp (continuous_const.add continuous_id).continuousOn hm) (hdf.comp (continuous_const.add continuous_id).continuousOn hm) (fun x hx => by
      have hh := (hd (a+x) ⟨by linarith [hx.1],by linarith [hx.2]⟩).comp x ((hasDerivAt_id x).const_add a)
      simpa only [Function.comp_def,mul_one] using hh)
    (by simpa using hfa) (by simpa using hfb)
  have hi : (∫ x in (0:ℝ)..(b-a), f (a+x)^2) = ∫ x in a..b, f x^2 := by
    simpa using intervalIntegral.integral_comp_add_left (f := fun x => f x^2) (a := 0) (b := b-a) a
  have hid : (∫ x in (0:ℝ)..(b-a), df (a+x)^2) = ∫ x in a..b, df x^2 := by
    simpa using intervalIntegral.integral_comp_add_left (f := fun x => df x^2) (a := 0) (b := b-a) a
  rwa [hi,hid] at h
private theorem second_order_unique_zero (a b Q : ℝ) (hab : a < b) (hQ : 0 ≤ Q) (u du q : ℝ → ℝ) (hu : ContinuousOn u (Icc a b)) (hdu : ContinuousOn du (Icc a b)) (hud : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x) (hdud : ∀ x ∈ Ioo a b, HasDerivAt du (q x*u x) x) (hqb : ∀ x ∈ Icc a b, |q x| ≤ Q) {ξ : ℝ} (hξ : ξ ∈ Ioo a b) (huz : u ξ=0) (hduz : du ξ=0) : ∀ x ∈ Icc a b, u x=0 ∧ du x=0 := by
  let E := fun x => u x^2+du x^2
  let dE := fun x => 2*u x*du x+2*du x*(q x*u x)
  have hEc : ContinuousOn E (Icc a b) := (hu.pow 2).add (hdu.pow 2)
  have hEd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt E (dE x) x := by
    convert ((hud x hx).pow 2).add ((hdud x hx).pow 2) using 1 <;> dsimp [dE] <;> ring
  have hEb (x : ℝ) (hx : x ∈ Icc a b) : ‖dE x‖ ≤ (1+Q)*‖E x‖ := by
    have hq := hqb x hx
    have h1 : |1+q x| ≤ 1+Q := by
      calc
        _ ≤ |(1:ℝ)|+|q x| := abs_add_le _ _
        _ ≤ _ := by simpa using add_le_add_left hq 1
    have habs : 2*|u x| *|du x| ≤ E x := by
      dsimp [E]; nlinarith [sq_nonneg (|u x|-|du x|),sq_abs (u x),sq_abs (du x)]
    have hnon : 0 ≤ E x := add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hnon]
    calc
      |dE x| = |1+q x| *(2*|u x| *|du x|) := by
        have he : dE x = (1+q x)*(2*u x*du x) := by dsimp [dE]; ring
        rw [he,abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      _ ≤ (1+Q)*E x := mul_le_mul h1 habs (by positivity) (by positivity)
  have hEz : E ξ=0 := by simp [E,huz,hduz]
  have hright := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := E) (f' := dE) (K := 1+Q) (a := ξ) (b := b) (hEc.mono (Icc_subset_Icc hξ.1.le le_rfl)) (fun x hx => (hEd x ⟨hξ.1.trans_le hx.1,hx.2⟩).hasDerivWithinAt) hEz (fun x hx => hEb x ⟨hξ.1.le.trans hx.1,hx.2.le⟩)
  have hleft := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := fun x => E (-x)) (f' := fun x => -dE (-x)) (K := 1+Q) (a := -ξ) (b := -a) (hEc.comp (continuous_neg.continuousOn) (fun x hx => ⟨by linarith [hx.2],by linarith [hx.1,hξ.2]⟩)) (fun x hx => by
      have hh := (hEd (-x) ⟨by linarith [hx.2],by linarith [hx.1,hξ.2]⟩).comp x (hasDerivAt_neg x)
      simpa only [Function.comp_def,mul_neg_one] using hh.hasDerivWithinAt)
    (by simpa using hEz)
    (fun x hx => by
      rw [norm_neg]; exact hEb (-x) ⟨by linarith [hx.2],by linarith [hx.1,hξ.2]⟩)
  intro x hx
  have hEx : E x=0 := by
    by_cases h : ξ≤x
    · exact hright x ⟨h,hx.2⟩
    · simpa using hleft (-x) ⟨by linarith,by linarith [hx.1]⟩
  dsimp [E] at hEx
  constructor <;> nlinarith [sq_nonneg (u x),sq_nonneg (du x)]
def fixedPotential (x : ℝ) : ℝ := x / 100
def fixedWeight (x : ℝ) : ℝ := 1 + (x - Real.pi / 2) / 100
private theorem fixed_potential_bounds {x : ℝ} (hx : x ∈ interval) : 0 ≤ fixedPotential x ∧ fixedPotential x < 1 / 25 := by
  change 0 ≤ x / 100 ∧ x / 100 < 1 / 25; change 0 ≤ x ∧ x ≤ Real.pi at hx
  constructor <;> linarith [Real.pi_lt_four]
private theorem fixed_weight_bounds {x : ℝ} (hx : x ∈ interval) : 49 / 50 < fixedWeight x ∧ fixedWeight x < 51 / 50 := by
  change 49 / 50 < 1 + (x - Real.pi / 2) / 100 ∧ 1 + (x - Real.pi / 2) / 100 < 51 / 50; change 0 ≤ x ∧ x ≤ Real.pi at hx
  constructor <;> linarith [Real.pi_lt_four]
private theorem fixed_potential_class : potentialClass 2 fixedPotential := by
  refine ⟨⟨?_, 1, ?_⟩, ?_, ?_⟩
  · unfold fixedPotential; fun_prop
  · intro x hx
    rw [abs_of_nonneg (fixed_potential_bounds hx).1]; linarith [(fixed_potential_bounds hx).2]
  · refine ⟨convex_Icc 0 Real.pi, ?_⟩
    intro x hx y hy a b ha hb hab; simp only [fixedPotential, smul_eq_mul]
    ring_nf
    exact le_refl _
  · intro x hx
    refine ⟨(fixed_potential_bounds hx).1, ?_⟩
    change (fixedPotential x : WithTop ℝ) ≤ ((2 : ℝ) : WithTop ℝ); exact WithTop.coe_le_coe.mpr (by linarith [(fixed_potential_bounds hx).2])
private theorem fixed_weight_class : weightClass (1 / 2) (3 / 2) fixedWeight := by
  refine ⟨⟨?_, 2, ?_⟩, ?_, ?_⟩
  · unfold fixedWeight; fun_prop
  · intro x hx
    obtain ⟨hl, hu⟩ := fixed_weight_bounds hx
    rw [abs_of_pos (by linarith : 0 < fixedWeight x)]; linarith
  · refine ⟨convex_Icc 0 Real.pi, ?_⟩
    intro x hx y hy a b ha hb hab; simp only [fixedWeight, smul_eq_mul]
    rw [show b = 1 - a by linarith]
    ring_nf
    exact le_refl _
  · intro x hx
    obtain ⟨hl, hu⟩ := fixed_weight_bounds hx
    constructor <;> linarith
private theorem bracket_gap_negative (a b a0 b0 : ℝ) (ha : 1015707960628 / 10^12 ≤ a) (hb : b ≤ 4015736948987 / 10^12) (ha0 : a0 ≤ 999989311927 / 10^12) (hb0 : 4000050992847 / 10^12 ≤ b0) : (b - a) - (b0 - a0) < -(3 / 100000) := by
  first | linarith
private theorem fixed_refutation_of_brackets (hbrackets : ∀ (e e0 : ℕ → ℝ), isSpectrum fixedPotential fixedWeight e → isSpectrum (fun _ => 0) fixedWeight e0 → 1015707960628 / 10^12 ≤ e 0 ∧ e 1 ≤ 4015736948987 / 10^12 ∧ e0 0 ≤ 999989311927 / 10^12 ∧ 4000050992847 / 10^12 ≤ e0 1) : ¬ claim := by
  intro hc
  obtain ⟨⟨⟨e, he⟩, ⟨e0, he0⟩⟩, hcomp⟩ :=
    hc 2 (1/2) (3/2) fixedPotential fixedWeight (by norm_num) (by norm_num) (by norm_num) fixed_potential_class fixed_weight_class
  obtain ⟨ha, hb, ha0, hb0⟩ := hbrackets e e0 he he0
  have hneg := bracket_gap_negative (e 0) (e 1) (e0 0) (e0 1) ha hb ha0 hb0
  have hle := hcomp e e0 he he0
  unfold gap at hle; linarith
private theorem series_zero_is_shooting {δ z : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (hz : z ∈ Icc (0:ℝ) 5) (hzero : (solution (aParameter z) (bParameter δ z) 1) = 0) : isShootingEigenvalue ((AffineMap.lineMap (0:ℝ) (δ/100))) fixedWeight z := by
  let A := aParameter z
  let B := bParameter δ z
  let u := fun x : ℝ => Real.pi * solution A B (x/Real.pi)
  have hp := Real.pi_pos
  have hpne := hp.ne'
  have hAB := parameter_bounds hδ hz
  have hscale {x : ℝ} (hx : x ∈ interval) : x/Real.pi ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg hx.1 hp.le, ?_⟩
    exact (div_le_one hp).2 hx.2
  have huc : ContinuousOn u interval := by
    apply continuousOn_const.mul; apply (solution_continuous A B hAB.1 hAB.2).comp (continuous_id.div_const Real.pi).continuousOn; intro x hx; exact hscale hx
  refine ⟨u,huc,?_,?_,?_,?_⟩
  · have hq : ContinuousOn (fun x => (AffineMap.lineMap (0:ℝ) (δ/100)) x-z*fixedWeight x) interval := by
      simp only [AffineMap.lineMap_apply_ring', sub_zero, add_zero, fixedWeight]
      fun_prop
    exact (hq.mul huc).intervalIntegrable_of_Icc (μ := volume) hp.le
  · have h0 := solution_volterra A B hAB.1 hAB.2 (x := 0) ⟨le_rfl,zero_le_one⟩
    simpa [u] using congrArg (fun v : ℝ => Real.pi*v) h0
  · have hs : solution A B 1 = 0 := by
      exact hzero
    simpa [u,hpne,hs]
  · intro x hx
    have hs := congrArg (fun v : ℝ => Real.pi*v) (solution_volterra A B hAB.1 hAB.2 (hscale hx))
    have hpx : Real.pi*(x/Real.pi)=x := by field_simp [hpne]
    have hsub := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := x/Real.pi) (fun r => (x-r)*((AffineMap.lineMap (0:ℝ) (δ/100)) r-z*fixedWeight r)*u r) Real.pi
    have hi : (∫ r in (0:ℝ)..x, (x-r)*((AffineMap.lineMap (0:ℝ) (δ/100)) r-z*fixedWeight r)*u r) = Real.pi * ∫ s in (0:ℝ)..(x/Real.pi), (x/Real.pi-s)*(A+B*s)*solution A B s := by
      calc
        _ = Real.pi * ∫ s in (0:ℝ)..(x/Real.pi), (x-Real.pi*s)*((AffineMap.lineMap (0:ℝ) (δ/100)) (Real.pi*s)-z*fixedWeight (Real.pi*s))*u (Real.pi*s) := by
          simpa only [smul_eq_mul,mul_zero,hpx] using hsub.symm
        _ = _ := by
          congr 1; congr 1; funext s; simp only [AffineMap.lineMap_apply_ring', sub_zero, add_zero]
          dsimp [u,A,B,aParameter,bParameter,fixedWeight]
          field_simp [hpne] <;> ring
    rw [hi]; simpa only [u,mul_add,hpx] using hs
private theorem endpoint_0 : 0 < (solution (aParameter (999989311923 / 1000000000000)) (bParameter 0 (999989311923 / 1000000000000)) 1) := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.aValue0 D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.bValue0 D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.a_bound0 D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.b_bound0
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.polynomial_sign0
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.aValue0 D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.bValue0 n) = (solution (aParameter (999989311923 / 1000000000000)) (bParameter 0 (999989311923 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.aValue_eq0,D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.Endpoint0.bValue_eq0]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_1 : (solution (aParameter (999989311927 / 1000000000000)) (bParameter 0 (999989311927 / 1000000000000)) 1) < 0 := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.aValue1 D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.bValue1 D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.a_bound1 D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.b_bound1
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.polynomial_sign1
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.aValue1 D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.bValue1 n) = (solution (aParameter (999989311927 / 1000000000000)) (bParameter 0 (999989311927 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.aValue_eq1,D5.S3.Analytic.SpectralGap.WeightedGapMajorant.Endpoint1.bValue_eq1]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_2 : (solution (aParameter (4000050992847 / 1000000000000)) (bParameter 0 (4000050992847 / 1000000000000)) 1) < 0 := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.aValue2 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.bValue2 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.a_bound2 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.b_bound2
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.polynomial_sign2
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.aValue2 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.bValue2 n) = (solution (aParameter (4000050992847 / 1000000000000)) (bParameter 0 (4000050992847 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.aValue_eq2,D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint2.bValue_eq2]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_3 : 0 < (solution (aParameter (4000050992851 / 1000000000000)) (bParameter 0 (4000050992851 / 1000000000000)) 1) := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.aValue3 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.bValue3 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.a_bound3 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.b_bound3
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.polynomial_sign3
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.aValue3 D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.bValue3 n) = (solution (aParameter (4000050992851 / 1000000000000)) (bParameter 0 (4000050992851 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.aValue_eq3,D5.S3.Analytic.SpectralGap.WeightedGapStateSeries.Endpoint3.bValue_eq3]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_4 : 0 < (solution (aParameter (253926990157 / 250000000000)) (bParameter 1 (253926990157 / 250000000000)) 1) := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.aValue4 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.bValue4 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.a_bound4 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.b_bound4
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.polynomial_sign4
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.aValue4 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.bValue4 n) = (solution (aParameter (253926990157 / 250000000000)) (bParameter 1 (253926990157 / 250000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.aValue_eq4,D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint4.bValue_eq4]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_5 : (solution (aParameter (126963495079 / 125000000000)) (bParameter 1 (126963495079 / 125000000000)) 1) < 0 := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.aValue5 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.bValue5 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.a_bound5 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.b_bound5
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.polynomial_sign5
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.aValue5 D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.bValue5 n) = (solution (aParameter (126963495079 / 125000000000)) (bParameter 1 (126963495079 / 125000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.aValue_eq5,D5.S3.Analytic.SpectralGap.WeightedGapDeterminant.Endpoint5.bValue_eq5]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_6 : (solution (aParameter (4015736948983 / 1000000000000)) (bParameter 1 (4015736948983 / 1000000000000)) 1) < 0 := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.aValue6 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.bValue6 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.a_bound6 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.b_bound6
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.polynomial_sign6
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.aValue6 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.bValue6 n) = (solution (aParameter (4015736948983 / 1000000000000)) (bParameter 1 (4015736948983 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.aValue_eq6,D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint6.bValue_eq6]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem endpoint_7 : 0 < (solution (aParameter (4015736948987 / 1000000000000)) (bParameter 1 (4015736948987 / 1000000000000)) 1) := by
  have ht := short_full_series_tail D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.aValue7 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.bValue7 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.a_bound7 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.b_bound7
  rw [← state_total] at ht
  have hs := D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.polynomial_sign7
  have htSmall := lt_of_le_of_lt ht short_remainder_lt
  clear ht
  rcases abs_lt.mp htSmall with ⟨htlo, hthi⟩
  have heq : (∑' n, coefficient D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.aValue7 D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.bValue7 n) = (solution (aParameter (4015736948987 / 1000000000000)) (bParameter 1 (4015736948987 / 1000000000000)) 1) := by
    simp only [solution, one_pow, mul_one]
    unfold aParameter bParameter; rw [D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.aValue_eq7,D5.S3.Analytic.SpectralGap.WeightedGapVolterra.Endpoint7.bValue_eq7]
  rw [heq] at htlo hthi
  linarith only [hs, htlo, hthi]
private theorem determinant_zero_between {δ a b : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (hab : a ≤ b) (hrange : Icc a b ⊆ Icc (0:ℝ) 5) (hs : ((solution (aParameter a) (bParameter δ a) 1) < 0 ∧ 0 < (solution (aParameter b) (bParameter δ b) 1)) ∨ (0 < (solution (aParameter a) (bParameter δ a) 1) ∧ (solution (aParameter b) (bParameter δ b) 1) < 0)) : ∃ z ∈ Icc a b, (solution (aParameter z) (bParameter δ z) 1)=0 := by
  have hc := (determinant_continuous hδ).mono hrange
  rcases hs with hs|hs
  · exact intermediate_value_Icc hab hc ⟨hs.1.le,hs.2.le⟩
  · exact intermediate_value_Icc' hab hc ⟨hs.2.le,hs.1.le⟩
private theorem root_0 : ∃ z ∈ Icc ((999989311923 / 1000000000000):ℝ) (999989311927 / 1000000000000), (solution (aParameter z) (bParameter 0 z) 1)=0 := by
  apply determinant_zero_between (by norm_num) (by norm_num)
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]
  · exact Or.inr ⟨endpoint_0,endpoint_1⟩
private theorem root_1 : ∃ z ∈ Icc ((4000050992847 / 1000000000000):ℝ) (4000050992851 / 1000000000000), (solution (aParameter z) (bParameter 0 z) 1)=0 := by
  apply determinant_zero_between (by norm_num) (by norm_num)
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]
  · exact Or.inl ⟨endpoint_2,endpoint_3⟩
private theorem root_2 : ∃ z ∈ Icc ((253926990157 / 250000000000):ℝ) (126963495079 / 125000000000), (solution (aParameter z) (bParameter 1 z) 1)=0 := by
  apply determinant_zero_between (by norm_num) (by norm_num)
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]
  · exact Or.inr ⟨endpoint_4,endpoint_5⟩
private theorem root_3 : ∃ z ∈ Icc ((4015736948983 / 1000000000000):ℝ) (4015736948987 / 1000000000000), (solution (aParameter z) (bParameter 1 z) 1)=0 := by
  apply determinant_zero_between (by norm_num) (by norm_num)
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]
  · exact Or.inl ⟨endpoint_6,endpoint_7⟩
private theorem interval_solution_separation (a b Q : ℝ) (hab : a < b) (f df q : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b)) (hq : ContinuousOn q (Icc a b)) (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) (hdfd : ∀ x ∈ Ioo a b, HasDerivAt df (q x*f x) x) (hqb : ∀ x ∈ Icc a b, -Q ≤ q x) (hfa : f a=0) (hfb : f b=0) (hne : ∃ x ∈ Icc a b, f x≠0) : 8 ≤ Q*(b-a)^2 := by
  have hiE : IntervalIntegrable (fun x => df x^2) volume a b :=
    (hdf.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  have hiM : IntervalIntegrable (fun x => f x^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  have hiq : IntervalIntegrable (fun x => q x*f x^2) volume a b :=
    (hq.mul (hf.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab.le
  have hM : 0 < ∫ x in a..b, f x^2 := by
    obtain ⟨x,hx,hne⟩ := hne
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℝ)) (Icc a b)) (hf.pow 2) (fun _ _ => sq_nonneg _) ⟨x,hx,sq_pos_of_ne_zero hne⟩
    simpa only [intervalIntegral.integral_zero,Pi.pow_apply] using h
  have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt (u := df) (u' := fun x => q x*f x) (v := f) (v' := df) (by simpa [uIcc_of_le hab.le] using hdf) (by simpa [uIcc_of_le hab.le] using hf) (by simpa [min_eq_left hab.le,max_eq_right hab.le] using hdfd) (by simpa [min_eq_left hab.le,max_eq_right hab.le] using hfd) ((hq.mul hf).intervalIntegrable_of_Icc (μ := volume) hab.le) (hdf.intervalIntegrable_of_Icc (μ := volume) hab.le)
  simp only [hfa,hfb,mul_zero,sub_self] at hp
  have heq : (∫ x in a..b, q x*f x*f x+df x*df x) = (∫ x in a..b, q x*f x^2)+(∫ x in a..b, df x^2) := by
    rw [← intervalIntegral.integral_add hiq hiE]; congr 1; funext x; ring
  rw [heq] at hp
  have hupper : (∫ x in a..b, df x^2) ≤ Q*(∫ x in a..b, f x^2) := by
    have hmono := intervalIntegral.integral_mono_on hab.le hiq.neg (hiM.const_mul Q) (fun x hx => by
        change -(q x*f x^2) ≤ Q*f x^2
        have hh : 0 ≤ q x+Q := by linarith [hqb x hx]
        nlinarith [mul_nonneg hh (sq_nonneg (f x))])
    change (∫ x in a..b, -(q x*f x^2)) ≤ (∫ x in a..b, Q*f x^2) at hmono; rw [intervalIntegral.integral_neg,intervalIntegral.integral_const_mul] at hmono; linarith
  have hpoin := interval_poincare a b hab f df hf hdf hfd hfa hfb
  have hbound : (∫ x in a..b, f x^2) ≤ (b-a)^2/8*Q*(∫ x in a..b, f x^2) := by
    calc _ ≤ (b-a)^2/8*(∫ x in a..b, df x^2) := hpoin
      _ ≤ (b-a)^2/8*(Q*(∫ x in a..b, f x^2)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  have hfactor : 1 ≤ (b-a)^2/8*Q := by
    apply (mul_le_mul_iff_right₀ hM).mp; nlinarith only [hbound]
  nlinarith
private theorem no_first_interior_zero (u : ℝ → ℝ) (hu0 : u 0=0) (hupi : u Real.pi=0) (hsep : ∀ a b : ℝ, 0≤a → a<b → b≤Real.pi → u a=0 → u b=0 → 8 ≤ 2*(b-a)^2) : ∀ x ∈ Ioo 0 Real.pi, u x≠0 := by
  intro x hx hzero
  have h1 := hsep 0 x le_rfl hx.1 hx.2.le hu0 hzero
  have h2 := hsep x Real.pi hx.1.le hx.2 le_rfl hzero hupi
  have hx2 : 19/10<x := by
    by_contra hh
    have hp : 0 ≤ (19/10-x)*(19/10+x) := mul_nonneg (by linarith) (by linarith [hx.1])
    nlinarith
  have hxp2 : 19/10<Real.pi-x := by
    by_contra hh
    have hp : 0≤(19/10-(Real.pi-x))*(19/10+(Real.pi-x)) :=
      mul_nonneg (by linarith) (by linarith [hx.2])
    nlinarith
  linarith [Real.pi_lt_d2]
private theorem at_most_one_interior_zero (u : ℝ → ℝ) (hu0 : u 0=0) (hupi : u Real.pi=0) (hsep : ∀ a b : ℝ, 0≤a → a<b → b≤Real.pi → u a=0 → u b=0 → 8 ≤ 5*(b-a)^2) : ∀ a ∈ Ioo 0 Real.pi, ∀ b ∈ Ioo 0 Real.pi, u a=0 → u b=0 → a=b := by
  have hlength (a b : ℝ) (hab : a<b) (h : 8≤5*(b-a)^2) : 6/5<b-a := by
    by_contra hh
    have hp : 0≤(6/5-(b-a))*(6/5+(b-a)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hnotlt (a b : ℝ) (ha : a ∈ Ioo 0 Real.pi) (hb : b ∈ Ioo 0 Real.pi) (hza : u a=0) (hzb : u b=0) (hab : a<b) : False := by
    have h1 := hlength 0 a ha.1 (hsep 0 a le_rfl ha.1 ha.2.le hu0 hza)
    have h2 := hlength a b hab (hsep a b ha.1.le hab hb.2.le hza hzb)
    have h3 := hlength b Real.pi hb.2 (hsep b Real.pi hb.1.le hb.2 le_rfl hzb hupi)
    linarith [Real.pi_lt_d2]
  intro a ha b hb hza hzb
  rcases lt_trichotomy a b with hh|hh|hh
  · exact (hnotlt a b ha hb hza hzb hh).elim
  · exact hh
  · exact (hnotlt b a hb ha hzb hza hh).elim
private theorem strong_subinterval_nonzero {V w u : ℝ → ℝ} {z Q : ℝ} (hu : strongEigenfunction V w z u) (hne : u ≠ 0) (hQ : 0≤Q) (hqb : ∀ x ∈ interval, |V x-z*w x|≤Q) {a b : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤Real.pi) : ∃ x ∈ Icc a b, u x≠0 := by
  by_contra hh
  push_neg at hh
  let m := (a+b)/2
  have hmab : m ∈ Ioo a b := ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
  have hm : m ∈ Ioo 0 Real.pi := Ioo_subset_Ioo ha hb hmab
  have hum : u m=0 := hh m ⟨hmab.1.le,hmab.2.le⟩
  have hevent : u =ᶠ[nhds m] (fun _ => (0:ℝ)) := by
    filter_upwards [Icc_mem_nhds hmab.1 hmab.2] with x hx
    exact hh x hx
  have hdu0 : derivWithin u interval m=0 :=
    (trial_hasDerivAt hu.1 hm).unique ((hasDerivAt_const m (0:ℝ)).congr_of_eventuallyEq hevent)
  have hz := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.second_order_unique_zero 0 Real.pi Q Real.pi_pos hQ u (derivWithin u interval) (fun x => V x-z*w x) hu.1.1.continuousOn (trial_derivative_continuous hu.1) (fun x hx => trial_hasDerivAt hu.1 hx) hu.2 hqb hm hum hdu0
  apply hne; funext x
  by_cases hx : x ∈ interval
  · exact (hz x hx).1
  · exact hu.1.2 x (fun hh => hx ⟨hh.1.le,hh.2.le⟩)
private theorem strong_zero_separation {V w u : ℝ → ℝ} {z Q : ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hu : strongEigenfunction V w z u) (hne : u≠0) (hQ : 0≤Q) (hqb : ∀ x ∈ interval, |V x-z*w x|≤Q) {a b : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤Real.pi) (hua : u a=0) (hub : u b=0) : 8≤Q*(b-a)^2 := by
  have hm : Icc a b ⊆ interval := Icc_subset_Icc ha hb
  exact D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.interval_solution_separation a b Q hab u (derivWithin u interval) (fun x => V x-z*w x) (hu.1.1.continuousOn.mono hm) ((trial_derivative_continuous hu.1).mono hm) ((hV.sub (hw.const_mul z)).mono hm) (fun x hx => trial_hasDerivAt hu.1 ⟨lt_of_le_of_lt ha hx.1,lt_of_lt_of_le hx.2 hb⟩) (fun x hx => hu.2 x ⟨lt_of_le_of_lt ha hx.1,lt_of_lt_of_le hx.2 hb⟩) (fun x hx => (abs_le.mp (hqb x (hm hx))).1) hua hub (strong_subinterval_nonzero hu hne hQ hqb ha hab hb)
private theorem continuous_nonzero_orientation (a b : ℝ) (hab : a<b) (u : ℝ → ℝ) (hu : ContinuousOn u (Icc a b)) (hnz : ∀ x ∈ Ioo a b, u x≠0) : (∀ x ∈ Ioo a b, 0<u x) ∨ (∀ x ∈ Ioo a b, u x<0) := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
  have hc := hu.mono Ioo_subset_Icc_self
  rcases lt_or_gt_of_ne (hnz m hm) with hmneg|hmpos
  · right
    intro x hx
    by_contra hh
    have hxp : 0<u x := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm (hnz x hx))
    obtain ⟨y,hy,he⟩ := isPreconnected_Ioo.intermediate_value hm hx hc ⟨hmneg.le,hxp.le⟩
    exact hnz y hy he
  · left
    intro x hx
    by_contra hh
    have hxn : u x<0 := lt_of_le_of_ne (le_of_not_gt hh) (hnz x hx)
    obtain ⟨y,hy,he⟩ := isPreconnected_Ioo.intermediate_value hx hm hc ⟨hxn.le,hmpos.le⟩
    exact hnz y hy he
private theorem strong_neg {V w u : ℝ → ℝ} {z : ℝ} (hu : strongEigenfunction V w z u) : strongEigenfunction V w z (fun x => -u x) := by
  refine ⟨⟨hu.1.1.neg,fun x hx => by simp [hu.1.2 x hx]⟩,?_⟩
  intro x hx
  have he : derivWithin (fun y => -u y) interval = fun y => -derivWithin u interval y := by
    funext y; exact derivWithin.fun_neg
  rw [he]
  convert (hu.2 x hx).neg using 1 <;>
    first | rfl | simp only [Pi.neg_apply,mul_neg]
private theorem strong_zero_derivative_ne_zero {V w u : ℝ → ℝ} {z Q ξ : ℝ} (hu : strongEigenfunction V w z u) (hne : u≠0) (hQ : 0≤Q) (hqb : ∀ x ∈ interval, |V x-z*w x|≤Q) (hξ : ξ ∈ Ioo 0 Real.pi) (hz : u ξ=0) : derivWithin u interval ξ≠0 := by
  intro hd
  have h := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.second_order_unique_zero 0 Real.pi Q Real.pi_pos hQ u (derivWithin u interval) (fun x => V x-z*w x) hu.1.1.continuousOn (trial_derivative_continuous hu.1) (fun x hx => trial_hasDerivAt hu.1 hx) hu.2 hqb hξ hz hd
  apply hne; funext x
  by_cases hx : x ∈ interval
  · exact (h x hx).1
  · exact hu.1.2 x (fun hh => hx ⟨hh.1.le,hh.2.le⟩)
private theorem impossible_positive_sides (u : ℝ → ℝ) (ξ d : ℝ) (hξ : ξ ∈ Ioo 0 Real.pi) (hz : u ξ=0) (hl : ∀ x ∈ Ioo 0 ξ, 0<u x) (hr : ∀ x ∈ Ioo ξ Real.pi, 0<u x) (hd : HasDerivAt u d ξ) (hdn : d≠0) : False := by
  have hmin : IsLocalMin u ξ := by
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with x hx
    rw [hz]
    rcases lt_trichotomy x ξ with hh|hh|hh
    · exact (hl x ⟨hx.1,hh⟩).le
    · subst x; simp [hz]
    · exact (hr x ⟨hh,hx.2⟩).le
  exact hdn (hmin.hasDerivAt_eq_zero hd)
private theorem simple_node_orientation {V w u : ℝ → ℝ} {z ξ : ℝ} (hu : strongEigenfunction V w z u) (hne : u≠0) (hξ : ξ ∈ Ioo 0 Real.pi) (hz : u ξ=0) (hunique : ∀ x ∈ Ioo 0 Real.pi, u x=0 → x=ξ) (hdn : derivWithin u interval ξ≠0) : ∃ v : ℝ → ℝ, strongEigenfunction V w z v ∧ v≠0 ∧ v ξ=0 ∧ (∀ x ∈ Ioo 0 ξ, 0<v x) ∧ (∀ x ∈ Ioo ξ Real.pi, v x<0) := by
  have hlset : Icc 0 ξ ⊆ interval := Icc_subset_Icc le_rfl hξ.2.le
  have hrset : Icc ξ Real.pi ⊆ interval := Icc_subset_Icc hξ.1.le le_rfl
  have hlnz : ∀ x ∈ Ioo 0 ξ, u x≠0 := by
    intro x hx he
    have hh := hunique x ⟨hx.1,hx.2.trans hξ.2⟩ he
    linarith [hx.2]
  have hrnz : ∀ x ∈ Ioo ξ Real.pi, u x≠0 := by
    intro x hx he
    have hh := hunique x ⟨hξ.1.trans hx.1,hx.2⟩ he
    linarith [hx.1]
  rcases continuous_nonzero_orientation 0 ξ hξ.1 u (hu.1.1.continuousOn.mono hlset) hlnz with hl|hl
  · rcases continuous_nonzero_orientation ξ Real.pi hξ.2 u (hu.1.1.continuousOn.mono hrset) hrnz with hr|hr
    · exact (impossible_positive_sides u ξ _ hξ hz hl hr (trial_hasDerivAt hu.1 hξ) hdn).elim
    · exact ⟨u,hu,hne,hz,hl,hr⟩
  · rcases continuous_nonzero_orientation ξ Real.pi hξ.2 u (hu.1.1.continuousOn.mono hrset) hrnz with hr|hr
    · refine ⟨(fun x => -u x),strong_neg hu,neg_ne_zero.mpr hne,by simp [hz],?_,?_⟩
      · intro x hx; exact neg_pos.mpr (hl x hx)
      · intro x hx; exact neg_neg_of_pos (hr x hx)
    · have hh := impossible_positive_sides (fun x => -u x) ξ (-derivWithin u interval ξ) hξ (by simp [hz]) (fun x hx => neg_pos.mpr (hl x hx)) (fun x hx => neg_pos.mpr (hr x hx)) (trial_hasDerivAt hu.1 hξ).neg (neg_ne_zero.mpr hdn)
      exact hh.elim
private theorem nozero_spectrum_lower {V w u : ℝ → ℝ} {z : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0<w x) (hu : strongEigenfunction V w z u) (hnz : ∀ x ∈ Ioo 0 Real.pi, u x≠0) (he : isSpectrum V w e) : z≤e 0 := by
  rcases continuous_nonzero_orientation 0 Real.pi Real.pi_pos u hu.1.1.continuousOn hnz with hp|hn
  · exact ground_spectrum_lower hV hw hwp hu hp he
  · exact ground_spectrum_lower hV hw hwp (strong_neg hu) (fun x hx => neg_pos.mpr (hn x hx)) he
private theorem first_shooting_root_is_minmax {V w : ℝ → ℝ} {z : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0<w x) (hqb : ∀ x ∈ interval, |V x-z*w x|≤2) (hz : isShootingEigenvalue V w z) (he : isSpectrum V w e) : e 0=z := by
  obtain ⟨u,hu,hune,_⟩ := shooting_regular hV hw hz
  have hsep (a b : ℝ) (ha : 0≤a) (hab : a<b) (hb : b≤Real.pi) (hua : u a=0) (hub : u b=0) : 8≤2*(b-a)^2 :=
    strong_zero_separation hV hw hu hune (by norm_num : (0:ℝ)≤2) hqb ha hab hb hua hub
  have hnz := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.no_first_interior_zero u (hu.1.2 0 (by simp)) (hu.1.2 Real.pi (by simp)) hsep
  exact le_antisymm (ground_spectrum_upper hV hw hu hune he) (nozero_spectrum_lower hV hw hwp hu hnz he)
private theorem second_shooting_root_is_minmax {V w : ℝ → ℝ} {z y : ℝ} {e : ℕ → ℝ} (hV : ContinuousOn V interval) (hw : ContinuousOn w interval) (hwp : ∀ x ∈ interval, 0<w x) (hqb : ∀ x ∈ interval, |V x-y*w x|≤5) (hz : isShootingEigenvalue V w z) (hy : isShootingEigenvalue V w y) (hzy : z<y) (he0 : e 0=z) (he : isSpectrum V w e) : e 1=y := by
  obtain ⟨u,hu,hune,_⟩ := shooting_regular hV hw hz
  obtain ⟨v,hv,hvne,_⟩ := shooting_regular hV hw hy
  have hsep (a b : ℝ) (ha : 0≤a) (hab : a<b) (hb : b≤Real.pi) (hva : v a=0) (hvb : v b=0) : 8≤5*(b-a)^2 :=
    strong_zero_separation hV hw hv hvne (by norm_num : (0:ℝ)≤5) hqb ha hab hb hva hvb
  have hunique := D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation.at_most_one_interior_zero v (hv.1.2 0 (by simp)) (hv.1.2 Real.pi (by simp)) hsep
  obtain ⟨ξ,hξ,hvξ⟩ : ∃ ξ ∈ Ioo 0 Real.pi, v ξ=0 := by
    by_contra hh
    push_neg at hh
    have hlo := nozero_spectrum_lower hV hw hwp hv hh he
    rw [he0] at hlo; linarith
  have hdn := strong_zero_derivative_ne_zero hv hvne (by norm_num : (0:ℝ)≤5) hqb hξ hvξ
  obtain ⟨v',hv',hvne',hvξ',hl,hr⟩ := simple_node_orientation hv hvne hξ hvξ (fun x hx hxz => hunique x hx ξ hξ hxz hvξ) hdn
  exact le_antisymm (second_spectrum_upper hV hw hwp hu hv' hune hvne' hzy he) (node_spectrum_lower hV hw hwp hv' hξ hvξ' hl hr he)
private theorem affine_q_bound {δ z K C : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (hz0 : 0≤z) (hzK : z≤K) (hK : 0≤K) (hC1 : 1/25≤C) (hCK : K*(51/50)≤C) : ∀ x ∈ interval, |(AffineMap.lineMap (0:ℝ) (δ/100)) x-z*fixedWeight x|≤C := by
  intro x hx
  have hwb := fixed_weight_bounds hx
  have hwlo : 49/50<fixedWeight x := by simpa [fixedWeight] using hwb.1
  have hwhi : fixedWeight x<51/50 := by simpa [fixedWeight] using hwb.2
  have hwp : 0≤fixedWeight x := by linarith
  have hax0 : 0≤δ*x := mul_nonneg hδ.1 hx.1
  have hax : δ*x≤x := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ.2) hx.1]
  have hV0 : 0≤(AffineMap.lineMap (0:ℝ) (δ/100)) x := by simp only [AffineMap.lineMap_apply_ring', sub_zero, add_zero]; nlinarith [hax0]
  have hVhi : (AffineMap.lineMap (0:ℝ) (δ/100)) x≤1/25 := by
    simp only [AffineMap.lineMap_apply_ring', sub_zero, add_zero]; nlinarith [hx.2,Real.pi_lt_four]
  have hzw0 : 0≤z*fixedWeight x := mul_nonneg hz0 hwp
  have hzwK : z*fixedWeight x≤K*(51/50) :=
    mul_le_mul hzK hwhi.le hwp hK
  rw [abs_le]
  constructor <;> linarith
theorem result : ¬ D5.S3.Analytic.SpectralGap.WeightedGapPolynomialCertificate.claim := by
  apply fixed_refutation_of_brackets; intro e e0 he he0
  obtain ⟨z00,hz00,hroot00⟩ := root_0
  obtain ⟨z01,hz01,hroot01⟩ := root_1
  obtain ⟨z10,hz10,hroot10⟩ := root_2
  obtain ⟨z11,hz11,hroot11⟩ := root_3
  have hV (δ : ℝ) : ContinuousOn ((AffineMap.lineMap (0:ℝ) (δ/100))) interval := by
    change ContinuousOn (fun x : ℝ => AffineMap.lineMap (0:ℝ) (δ/100) x) interval
    simp only [AffineMap.lineMap_apply_ring', sub_zero, add_zero]
    fun_prop
  have hW : ContinuousOn fixedWeight interval := by unfold fixedWeight; fun_prop
  have hWP : ∀ x ∈ interval, 0<fixedWeight x := by
    intro x hx
    have hh := fixed_weight_bounds hx
    change 49/50<fixedWeight x ∧ fixedWeight x<51/50 at hh; linarith [hh.1]
  have he' : isSpectrum ((AffineMap.lineMap (0:ℝ) (1/100))) fixedWeight e := by
    have hVeq : (AffineMap.lineMap (0:ℝ) (1/100) : ℝ → ℝ) = fixedPotential := by
      funext x; simp [AffineMap.lineMap_apply_ring', fixedPotential, div_eq_mul_inv]
    rw [hVeq]; exact he
  have he0' : isSpectrum ((AffineMap.lineMap (0:ℝ) (0/100))) fixedWeight e0 := by
    have hVeq : (AffineMap.lineMap (0:ℝ) (0/100) : ℝ → ℝ) = (fun _ : ℝ => 0) := by
      funext x; simp [AffineMap.lineMap_apply_ring']
    rw [hVeq]; exact he0
  have hs00 := series_zero_is_shooting (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) (show z00 ∈ Icc (0:ℝ) 5 by constructor <;> linarith [hz00.1,hz00.2]) hroot00
  have hs01 := series_zero_is_shooting (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1) (show z01 ∈ Icc (0:ℝ) 5 by constructor <;> linarith [hz01.1,hz01.2]) hroot01
  have hs10 := series_zero_is_shooting (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) (show z10 ∈ Icc (0:ℝ) 5 by constructor <;> linarith [hz10.1,hz10.2]) hroot10
  have hs11 := series_zero_is_shooting (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) (show z11 ∈ Icc (0:ℝ) 5 by constructor <;> linarith [hz11.1,hz11.2]) hroot11
  have he00 : e0 0=z00 := first_shooting_root_is_minmax (hV 0) hW hWP (affine_q_bound (K := 11/10) (by norm_num) (by linarith [hz00.1]) (by linarith [hz00.2]) (by norm_num) (by norm_num) (by norm_num)) hs00 he0'
  have he01 : e0 1=z01 := second_shooting_root_is_minmax (hV 0) hW hWP (affine_q_bound (K := 41/10) (by norm_num) (by linarith [hz01.1]) (by linarith [hz01.2]) (by norm_num) (by norm_num) (by norm_num)) hs00 hs01 (by linarith [hz00.2,hz01.1]) he00 he0'
  have he10 : e 0=z10 := first_shooting_root_is_minmax (hV 1) hW hWP (affine_q_bound (K := 11/10) (by norm_num) (by linarith [hz10.1]) (by linarith [hz10.2]) (by norm_num) (by norm_num) (by norm_num)) hs10 he'
  have he11 : e 1=z11 := second_shooting_root_is_minmax (hV 1) hW hWP (affine_q_bound (K := 41/10) (by norm_num) (by linarith [hz11.1]) (by linarith [hz11.2]) (by norm_num) (by norm_num) (by norm_num)) hs10 hs11 (by linarith [hz10.2,hz11.1]) he10 he'
  rw [he10,he11,he00,he01]
  constructor
  · linarith [hz10.1]
  constructor
  · linarith [hz11.2]
  constructor
  · linarith [hz00.2]
  · linarith [hz01.1]
end D5.S3.Analytic.SpectralGap.WeightedConvexPotentialRefutation
end
