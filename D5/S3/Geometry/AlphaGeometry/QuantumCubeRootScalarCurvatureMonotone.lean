/- GID: D5/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/QuantumCubeRootScalarCurvatureMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantum cube-root scalar curvature is strictly Schur-increasing. -/

/-
admission_basis: escape-witness
escape_witness: scal3_eq_spectral_ratio
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15716
DTR reading: DTR-Unregistered. No Reg mirror is delivered. The source-family registration lacks a law-violating variation, whole-family slot sensitivity, and actual observational-dependence proofs.
The tangent-normal frame transports coordinate curvature to the spectral ratio. Transport identities are consumed normalization helpers in this module. The faithful-state order uses the frozen PositiveSimplexGeometryAndMixing.moreMixed.
Direct frozen dependencies: the declaration identities below.
F1: D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.moreMixed_positive_chain; declaration statement_id=sha256:f19ea714dc2955a566704efc00c1ce31eb52e2401a946d90a2c48a02479565f6
F2: D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.IsTTransform; declaration statement_id=sha256:42e55cff12a5c9f54284d516691bb017d9d7182af2419124015df29f459afefc
F3: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P; declaration statement_id=sha256:a10d641664aaff2022a38c921d56a39f9764079f2823390614fec9abe97aa86d
F4: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P_evalSum; declaration statement_id=sha256:7754691acf8f98426f2359983e218acaea91f977130664f3d71b32bc3cdf3e47
F5: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_le_sum_sq; declaration statement_id=sha256:13e938553d0487fbdba26676b6929f9f746a6568371cb9df26c2616d69dc626a
F6: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.PositiveT; declaration statement_id=sha256:6af391fa094c3e0f33c4f7c75181c22e1e3e1c7a571edd9abd444a08b4d0b83a
F7: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed; declaration statement_id=sha256:565b9b70d03155f061b4fe949164aa173255e7ceac42365730d8420ff3c7616a
F8: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.simplex; declaration statement_id=sha256:c3964d9a4646b69a3c4c6a66ca1cb9591d79f2dcbb20c146af611d50469eeed8
F9: D5/S3/Weil/ZetaLinear/PosIndex.rtrace; declaration statement_id=sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F10: D5/S3/Weil/ZetaLinear/HermitianPosPart.rtrace_specMap; declaration statement_id=sha256:efa5f0bbdc4f0443275c16da086085a95c6f4e6395761aa1fadb48ed96f8ca46
F11: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap; declaration statement_id=sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
Per-declaration classification; non-proposition definitions carry no content claim.
proof_shape: densityStates: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.claim, QuantumCubeRootScalarCurvatureMonotone.density_eig_simplex, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio, QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: none
proof_shape: metric: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.scal3, QuantumCubeRootScalarCurvatureMonotone.metric_eq_nine_rootMetric, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: none
proof_shape: scal3: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.claim, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio, QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: none
proof_shape: eig: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.claim, QuantumCubeRootScalarCurvatureMonotone.density_eig_simplex, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio, QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: none
proof_shape: claim: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: F7
proof_shape: inverse_scale: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_scale, QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_dilation; frozen_dependencies: none
proof_shape: entry_derivative_scale: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_scale; frozen_dependencies: none
proof_shape: christoffel_scale: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_scale_eventually, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_scale; frozen_dependencies: none
proof_shape: christoffel_scale_eventually: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_scale; frozen_dependencies: none
proof_shape: ricci_scale: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_dilation; frozen_dependencies: none
proof_shape: scalar_curvature_dilation: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.scalar_curvature_embedding_dilation_three; frozen_dependencies: none
proof_shape: scalar_curvature_embedding_dilation_three: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: christoffel_congr_nhds: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.christoffel_eventually_congr, QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_congr_nhds; frozen_dependencies: none
proof_shape: christoffel_eventually_congr: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.ricci_congr_nhds; frozen_dependencies: none
proof_shape: ricci_congr_nhds: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.Transport.scalarCurvature_congr_nhds; frozen_dependencies: none
proof_shape: scalarCurvature_congr_nhds: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: hermBilinearLin: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.hermBilinear; frozen_dependencies: none
proof_shape: hermBilinear: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.secondForm, QuantumCubeRootScalarCurvatureMonotone.B_symm, QuantumCubeRootScalarCurvatureMonotone.B_smooth, QuantumCubeRootScalarCurvatureMonotone.B_fderiv, QuantumCubeRootScalarCurvatureMonotone.N_unit, QuantumCubeRootScalarCurvatureMonotone.N_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.dual, QuantumCubeRootScalarCurvatureMonotone.dual_apply, QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.b_symm, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: none
proof_shape: frameMetric: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.frameMetric_posdef, QuantumCubeRootScalarCurvatureMonotone.rootMetric; frozen_dependencies: none
proof_shape: frameMetric_posdef: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.rootMetric_posdef; frozen_dependencies: none
proof_shape: tangentFrame: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.rootMetric, QuantumCubeRootScalarCurvatureMonotone.tangentFrame_independent, QuantumCubeRootScalarCurvatureMonotone.rootMetric_posdef, QuantumCubeRootScalarCurvatureMonotone.metric_eq_nine_rootMetric, QuantumCubeRootScalarCurvatureMonotone.de, QuantumCubeRootScalarCurvatureMonotone.frame_smooth, QuantumCubeRootScalarCurvatureMonotone.de_smooth, QuantumCubeRootScalarCurvatureMonotone.metric_entry_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_second, QuantumCubeRootScalarCurvatureMonotone.de_mixed, QuantumCubeRootScalarCurvatureMonotone.N_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.dual, QuantumCubeRootScalarCurvatureMonotone.dual_apply, QuantumCubeRootScalarCurvatureMonotone.metric_symmetric, QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.immersion_derivative_expansion, QuantumCubeRootScalarCurvatureMonotone.dual_derivative, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: none
proof_shape: rootMetric: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.rootMetric_posdef, QuantumCubeRootScalarCurvatureMonotone.metric_eq_nine_rootMetric, QuantumCubeRootScalarCurvatureMonotone.metric_entry_smooth, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.dual, QuantumCubeRootScalarCurvatureMonotone.dual_apply, QuantumCubeRootScalarCurvatureMonotone.metric_isUnit, QuantumCubeRootScalarCurvatureMonotone.metric_symmetric, QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.inverse_metric_smooth, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss, QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar, QuantumCubeRootScalarCurvatureMonotone.shapeMatrix, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: tangentFrame_independent: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.rootMetric_posdef; frozen_dependencies: none
proof_shape: rootMetric_posdef: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.metric_isUnit; frozen_dependencies: none
proof_shape: metric_eq_nine_rootMetric: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: normalFunctional: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.normalFunctional_apply, QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective, QuantumCubeRootScalarCurvatureMonotone.shape, QuantumCubeRootScalarCurvatureMonotone.shape_gauss_spectral; frozen_dependencies: none
proof_shape: normalFunctional_apply: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective; frozen_dependencies: none
proof_shape: immersion_normal_tangent: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective, QuantumCubeRootScalarCurvatureMonotone.N_orthogonal, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.DN_shape_derivative; frozen_dependencies: F9,F10,F11
proof_shape: fullFrame: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrame_apply, QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective, QuantumCubeRootScalarCurvatureMonotone.fullFrameEquiv, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate; frozen_dependencies: none
proof_shape: fullFrame_apply: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate; frozen_dependencies: none
proof_shape: fullFrame_injective: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrameEquiv; frozen_dependencies: F9,F10,F11
proof_shape: fullFrame_finrank: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.fullFrameEquiv; frozen_dependencies: none
proof_shape: fullFrameEquiv: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate, QuantumCubeRootScalarCurvatureMonotone.shape_trace, QuantumCubeRootScalarCurvatureMonotone.shape_square_trace; frozen_dependencies: F9,F10,F11
proof_shape: de: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.secondForm, QuantumCubeRootScalarCurvatureMonotone.de_smooth, QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_second, QuantumCubeRootScalarCurvatureMonotone.de_symm, QuantumCubeRootScalarCurvatureMonotone.de_mixed, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.b_symm, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: secondForm: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.b_symm, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss, QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar, QuantumCubeRootScalarCurvatureMonotone.shapeMatrix, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss; frozen_dependencies: none
proof_shape: B_symm: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.metric_symmetric, QuantumCubeRootScalarCurvatureMonotone.dual_N; frozen_dependencies: none
proof_shape: B_smooth: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.metric_entry_smooth, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth; frozen_dependencies: none
proof_shape: B_fderiv: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; frozen_dependencies: none
proof_shape: frame_smooth: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.de_smooth, QuantumCubeRootScalarCurvatureMonotone.metric_entry_smooth, QuantumCubeRootScalarCurvatureMonotone.de_mixed, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: de_smooth: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth; frozen_dependencies: none
proof_shape: N_smooth: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: F9,F10,F11
proof_shape: b_smooth: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: F9,F10,F11
proof_shape: metric_entry_smooth: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.inverse_metric_smooth; frozen_dependencies: none
proof_shape: frame_second: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.de_symm; frozen_dependencies: none
proof_shape: de_symm: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.b_symm, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: de_mixed: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: N_unit: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; frozen_dependencies: F9,F10,F11
proof_shape: N_orthogonal: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N; frozen_dependencies: F9,F10,F11
proof_shape: DN_orthogonal: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: F9,F10,F11
proof_shape: DN_frame: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_dual; frozen_dependencies: F9,F10,F11
proof_shape: christoffel_frame: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: dual: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.dual_apply, QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.dual_derivative, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: none
proof_shape: dual_apply: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.DN_dual; frozen_dependencies: none
proof_shape: metric_isUnit: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.inverse_metric_smooth, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: metric_symmetric: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar; frozen_dependencies: none
proof_shape: dual_frame: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.dual_derivative, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: dual_N: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: F9,F10,F11
proof_shape: immersion_derivative_expansion: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.dual_derivative, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: none
proof_shape: dual_derivative: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; frozen_dependencies: none
proof_shape: frame_decomposition: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; consumers: QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: F9,F10,F11
proof_shape: inverse_metric_smooth: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth; frozen_dependencies: none
proof_shape: christoffel_smooth: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: none
proof_shape: frame_structure: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci; frozen_dependencies: F9,F10,F11
proof_shape: b_symm: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector; frozen_dependencies: none
proof_shape: DN_dual: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector; frozen_dependencies: F9,F10,F11
proof_shape: coordinate_ricci: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss; frozen_dependencies: F9,F10,F11
proof_shape: ricci_matrix_gauss: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar; frozen_dependencies: F9,F10,F11
proof_shape: coordinate_gauss_scalar: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss; frozen_dependencies: F9,F10,F11
proof_shape: jordan_normal_val: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.jordan_square_normal_val, QuantumCubeRootScalarCurvatureMonotone.inner_normal_jordan_normal; frozen_dependencies: none
proof_shape: jordan_square_normal_val: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.inner_normal_jordan_square_normal; frozen_dependencies: none
proof_shape: inner_normal_jordan_normal: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_gauss_spectral; frozen_dependencies: none
proof_shape: inner_normal_jordan_square_normal: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_gauss_spectral; frozen_dependencies: none
proof_shape: shape: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_gauss_spectral, QuantumCubeRootScalarCurvatureMonotone.shape_apply, QuantumCubeRootScalarCurvatureMonotone.shape_normal, QuantumCubeRootScalarCurvatureMonotone.DN_shape_derivative, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate, QuantumCubeRootScalarCurvatureMonotone.shape_trace, QuantumCubeRootScalarCurvatureMonotone.shape_square_trace, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
proof_shape: shape_gauss_spectral: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: F3,F4,F9,F10,F11
proof_shape: shapeMatrix: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate, QuantumCubeRootScalarCurvatureMonotone.shape_trace, QuantumCubeRootScalarCurvatureMonotone.shape_square_trace, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss; frozen_dependencies: none
proof_shape: shape_apply: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_normal, QuantumCubeRootScalarCurvatureMonotone.DN_shape_derivative; frozen_dependencies: none
proof_shape: shape_normal: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_conjugate; frozen_dependencies: none
proof_shape: DN_shape_derivative: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_conjugate; frozen_dependencies: F9,F10,F11
proof_shape: pi_derivative_expansion: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector; frozen_dependencies: none
proof_shape: DN_dual_vector: content; escape_witness: HermitianCubeDerivative.cube_derivative_kernel; consumers: QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame; frozen_dependencies: F9,F10,F11
proof_shape: DN_fullFrame: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_conjugate; frozen_dependencies: F9,F10,F11
proof_shape: shape_conjugate: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; consumers: QuantumCubeRootScalarCurvatureMonotone.shape_trace, QuantumCubeRootScalarCurvatureMonotone.shape_square_trace; frozen_dependencies: F9,F10,F11
proof_shape: shape_trace: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss; frozen_dependencies: F9,F10,F11
proof_shape: shape_square_trace: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.frame_decomposition; consumers: QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss; frozen_dependencies: F9,F10,F11
proof_shape: coordinate_shape_gauss: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: F9,F10,F11
proof_shape: root_trace_pow: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.root_moment; frozen_dependencies: none
proof_shape: root_moment: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.root_spectral_ratio; frozen_dependencies: F3,F4,F9,F10,F11
proof_shape: root_spectral_ratio: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: F3,F4,F9,F10,F11
proof_shape: density_eig_simplex: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: F8
proof_shape: chart_scalar_spectral: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.christoffel_frame; consumers: QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: F3,F4,F9,F10,F11
proof_shape: scal3_eq_spectral_ratio: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; consumers: QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: F3,F4,F9,F10,F11
proof_shape: result: content; escape_witness: QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; consumers: terminal result; frozen_dependencies: F1,F2,F3,F4,F5,F6,F7,F8,F9,F10,F11
-/


import D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative
import D5.S3.Geometry.AlphaGeometry.HermitianHypersurfaceCalculus
import D5.S3.Geometry.AlphaGeometry.CoordinateCurvatureMajorization
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix Topology Matrix.Norms.Elementwise
open Filter
namespace D5.S3.Geometry.AlphaGeometry.QuantumCubeRootScalarCurvatureMonotone

open D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates
open D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative
open D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.Traces
open D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss
open D5.S3.Geometry.AlphaGeometry.CoordinateCurvatureMajorization
open D5.S3.Geometry.AlphaGeometry.PairCurvatureInequality
def densityStates (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {A | A.PosDef ∧ A.trace = 1}
def metric {n : ℕ} (x : Fin (n^2-1) → ℝ) : Matrix (Fin (n^2-1)) (Fin (n^2-1)) ℝ :=
  fun i j => herm_inner
    (fderiv ℝ (alphaEmbed3 ∘ rho) x (Pi.single i 1))
    (fderiv ℝ (alphaEmbed3 ∘ rho) x (Pi.single j 1))
def scal3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  scalarCurvature metric (chartPoint A)
def eig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ :=
  if h : A.IsHermitian then h.eigenvalues else 0
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
  A ∈ densityStates n → B ∈ densityStates n →
  D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.moreMixed (eig A) (eig B) →
    scal3 B ≤ scal3 A ∧
    ((¬ ∃ pi : Equiv.Perm (Fin n), eig A = eig B ∘ pi) → scal3 B < scal3 A)
namespace Transport
section
set_option backward.isDefEq.respectTransparency false
open Filter Matrix
variable {m : ℕ}
private lemma inverse_scale (c : ℝ) (hc : c ≠ 0) (A : (Matrix (Fin m) (Fin m) ℝ)) (hA : IsUnit A.det) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  letI : Invertible c := invertibleOfNonzero hc
  simpa only [invOf_eq_inv] using Matrix.inv_smul A c hA
private lemma entry_derivative_scale (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (c : ℝ) (x : (Fin m → ℝ)) (i j : Fin m) :
    fderiv ℝ (fun t => (c • g t) i j) x = c • fderiv ℝ (fun t => g t i j) x := by
  exact congrFun (fderiv_const_smul_field c (f := fun t => g t i j)) x
private lemma christoffel_scale (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (c : ℝ) (hc : c ≠ 0) (x : (Fin m → ℝ))
    (hg : IsUnit (g x).det) (k i j : Fin m) :
    christoffel (fun t => c • g t) x k i j = christoffel g x k i j := by
  unfold christoffel
  rw [inverse_scale c hc (g x) hg]
  simp_rw [entry_derivative_scale]
  simp only [Matrix.smul_apply,smul_eq_mul,ContinuousLinearMap.smul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  field_simp
  <;> ring
private lemma christoffel_scale_eventually (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (c : ℝ) (hc : c ≠ 0) (x : (Fin m → ℝ))
    (hg : ∀ᶠ t in 𝓝 x, IsUnit (g t).det) (k i j : Fin m) :
    (fun t => christoffel (fun z => c • g z) t k i j) =ᶠ[𝓝 x]
      (fun t => christoffel g t k i j) := by
  filter_upwards [hg] with t ht
  exact christoffel_scale g c hc t ht k i j
private lemma ricci_scale (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (c : ℝ) (hc : c ≠ 0) (x : (Fin m → ℝ))
    (hg : ∀ᶠ t in 𝓝 x, IsUnit (g t).det) (i j : Fin m) :
    ricci (fun t => c • g t) x i j = ricci g x i j := by
  have hx : IsUnit (g x).det := hg.self_of_nhds
  unfold ricci
  apply Finset.sum_congr rfl
  intro k _
  rw [(christoffel_scale_eventually g c hc x hg k i j).fderiv_eq,
    (christoffel_scale_eventually g c hc x hg k i k).fderiv_eq]
  simp_rw [christoffel_scale g c hc x hx]
private theorem scalar_curvature_dilation (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (c : ℝ) (hc : c ≠ 0) (x : (Fin m → ℝ))
    (hg : ∀ᶠ t in 𝓝 x, IsUnit (g t).det) :
    scalarCurvature (fun t => c • g t) x = c⁻¹ * scalarCurvature g x := by
  unfold scalarCurvature
  rw [inverse_scale c hc (g x) hg.self_of_nhds]
  simp_rw [ricci_scale g c hc x hg]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem scalar_curvature_embedding_dilation_three (g : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (x : (Fin m → ℝ))
    (hg : ∀ᶠ t in 𝓝 x, IsUnit (g t).det) :
    scalarCurvature (fun t => (9 : ℝ) • g t) x = (1/9 : ℝ) * scalarCurvature g x := by
  simpa using scalar_curvature_dilation g 9 (by norm_num) x hg
end
section
set_option backward.isDefEq.respectTransparency false
open Filter
variable {m : ℕ}
private lemma christoffel_congr_nhds (g h : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (x : (Fin m → ℝ)) (heq : g =ᶠ[𝓝 x] h)
    (k i j : Fin m) : christoffel g x k i j = christoffel h x k i j := by
  have hd (a b : Fin m) : fderiv ℝ (fun t => g t a b) x = fderiv ℝ (fun t => h t a b) x := by
    have hh : (fun t => g t a b) =ᶠ[𝓝 x] (fun t => h t a b) := heq.mono (fun _ hz => congrArg (fun A : (Matrix (Fin m) (Fin m) ℝ) => A a b) hz)
    exact hh.fderiv_eq
  unfold christoffel
  rw [heq.eq_of_nhds]
  simp_rw [hd]
private lemma christoffel_eventually_congr (g h : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (x : (Fin m → ℝ)) (heq : g =ᶠ[𝓝 x] h)
    (k i j : Fin m) :
    (fun t => christoffel g t k i j) =ᶠ[𝓝 x] (fun t => christoffel h t k i j) := by
  filter_upwards [heq.eventuallyEq_nhds] with t ht
  exact christoffel_congr_nhds g h t ht k i j
private lemma ricci_congr_nhds (g h : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (x : (Fin m → ℝ)) (heq : g =ᶠ[𝓝 x] h)
    (i j : Fin m) : ricci g x i j = ricci h x i j := by
  have hd (a b c : Fin m) :
      fderiv ℝ (fun t => christoffel g t a b c) x = fderiv ℝ (fun t => christoffel h t a b c) x :=
    (christoffel_eventually_congr g h x heq a b c).fderiv_eq
  unfold ricci
  simp_rw [hd,christoffel_congr_nhds g h x heq]
private theorem scalarCurvature_congr_nhds (g h : (Fin m → ℝ) → (Matrix (Fin m) (Fin m) ℝ)) (x : (Fin m → ℝ)) (heq : g =ᶠ[𝓝 x] h) :
    scalarCurvature g x = scalarCurvature h x := by
  unfold scalarCurvature
  rw [heq.eq_of_nhds]
  simp_rw [ricci_congr_nhds g h x heq]
end
end Transport
open Transport
set_option backward.isDefEq.respectTransparency false
section Bilinear
open scoped Matrix.Norms.Elementwise
private def hermBilinearLin (n : ℕ) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →ₗ[ℝ] (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →ₗ[ℝ] ℝ :=
  (((LinearMap.mul ℝ (A := (Matrix (Fin n) (Fin n) ℂ))).compr₂
    (Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ))).compl₁₂
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype)
private def hermBilinear (n : ℕ) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →L[ℝ] (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →L[ℝ] ℝ := (hermBilinearLin n).toContinuousBilinearMap
end Bilinear
private def frameMetric {n m : ℕ} (e : Fin m → (Fin m → ℝ) → (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => herm_inner (e i x).val (e j x).val
private lemma frameMetric_posdef {n m : ℕ} (e : Fin m → (Fin m → ℝ) → (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (x : Fin m → ℝ)
    (he : LinearIndependent ℝ (fun i => e i x)) : (frameMetric e x).PosDef := by
  letI : NormedAddCommGroup ((Matrix (Fin n) (Fin n) ℂ)) := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup 1 Matrix.PosSemidef.one
  letI : InnerProductSpace ℂ ((Matrix (Fin n) (Fin n) ℂ)) := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
  letI : InnerProductSpace ℝ ((Matrix (Fin n) (Fin n) ℂ)) := InnerProductSpace.rclikeToReal ℂ ((Matrix (Fin n) (Fin n) ℂ))
  have hi (A B : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) : inner ℝ A B = herm_inner A.val B.val := by
    change (B.val*1*A.valᴴ).trace.re = (A.val*B.val).trace.re
    rw [Matrix.mul_one,A.property.isHermitian.eq,Matrix.trace_mul_comm]
  have hg : Matrix.gram ℝ (fun i => e i x) = frameMetric e x := by ext i j; exact hi _ _
  rw [← hg]
  exact Matrix.posDef_gram_of_linearIndependent he
private def tangentFrame {n : ℕ} (i : Fin (n^2-1)) (x : (Fin (n ^ 2 - 1) → ℝ)) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  fderiv ℝ immersion x (Pi.single i 1)
private def rootMetric {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) : Matrix (Fin (n^2-1)) (Fin (n^2-1)) ℝ :=
  frameMetric (@tangentFrame n) x
private lemma tangentFrame_independent {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    LinearIndependent ℝ (fun i => tangentFrame i x) := by
  simpa only [tangentFrame,Function.comp_def,Pi.basisFun_apply,ContinuousLinearMap.coe_coe] using (Pi.basisFun ℝ (Fin (n^2-1))).linearIndependent.map'
    (fderiv ℝ immersion x).toLinearMap (LinearMap.ker_eq_bot.mpr (immersion_derivative_injective hn x hx))
private lemma rootMetric_posdef {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    (rootMetric x).PosDef := frameMetric_posdef _ _ (tangentFrame_independent hn x hx)
private lemma metric_eq_nine_rootMetric {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    metric x = (9 : ℝ) • rootMetric x := by
  have hf : alphaEmbed3 ∘ (@rho n) = (fun t : (Fin (n ^ 2 - 1) → ℝ) => (3 : ℝ) • (immersion t).val) := by
    funext t
    simp only [Function.comp_apply,alphaEmbed3,immersion,D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.root,
      D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.rhoH_val]
    rfl
  have hd := ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).subtypeL.hasFDerivAt.comp x
    ((immersion_contDiffAt x hx).differentiableAt (by simp)).hasFDerivAt
  ext i j
  change herm_inner (fderiv ℝ (alphaEmbed3 ∘ rho) x (Pi.single i 1))
    (fderiv ℝ (alphaEmbed3 ∘ rho) x (Pi.single j 1)) = 9*herm_inner (tangentFrame i x).val (tangentFrame j x).val
  rw [hf]
  have hs := hd.const_smul (3 : ℝ)
  change HasFDerivAt (fun t : (Fin (n ^ 2 - 1) → ℝ) => (3 : ℝ) • (immersion t).val) _ x at hs
  rw [hs.fderiv]
  change herm_inner ((3 : ℝ) • (tangentFrame i x).val) ((3 : ℝ) • (tangentFrame j x).val) = _
  rw [herm_inner_smul_left,herm_inner_smul_right]
  ring
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private def normalFunctional {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →L[ℝ] ℝ :=
  ((Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap)).comp (((LinearMap.mul ℝ (A := Matrix (Fin n) (Fin n) ℂ)).toContinuousBilinearMap (normal Y).val).comp ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).subtypeL)
private lemma normalFunctional_apply {n : ℕ} (Y V : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :
    normalFunctional Y V = herm_inner (normal Y).val V.val := rfl
private lemma immersion_normal_tangent {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ))
    (hx : (rho x).PosDef) (V : (Fin (n ^ 2 - 1) → ℝ)) :
    herm_inner (normal (immersion x)).val (fderiv ℝ immersion x V).val = 0 := by
  have hp : (rhoH x).val.PosDef := by rwa [rhoH_val]
  have hroot := root_posdef (rhoH x) hp
  have hS : 0 < S4 (immersion x) := S4_pos hn _ hroot
  have hf := (immersion_contDiffAt x hx).differentiableAt (by simp)
  have hd := (F_hasFDerivAt (immersion x)).comp x hf.hasFDerivAt
  have he : (F ∘ (@immersion n)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n |>.mem_nhds hx] with t ht
    exact immersion_level_one hn t ht
  have hdf := he.fderiv_eq (𝕜 := ℝ)
  rw [hd.fderiv] at hdf
  have hc : fderiv ℝ (fun _ : (Fin (n ^ 2 - 1) → ℝ) => (1 : ℝ)) x = 0 := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).fderiv
  rw [hc] at hdf
  have hz := congrArg (fun L : (Fin (n ^ 2 - 1) → ℝ) →L[ℝ] ℝ => L V) hdf
  have hg : fderiv ℝ F (immersion x) (fderiv ℝ immersion x V) = 0 := by
    simpa only [(F_hasFDerivAt (immersion x)).fderiv,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using hz
  rw [DF_normal _ _ hS] at hg
  exact (mul_eq_zero.mp hg).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr hS)))
private def fullFrame {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) : (Fin (n ^ 2 - 1) → ℝ) × ℝ →L[ℝ] (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (fderiv ℝ immersion x).comp (ContinuousLinearMap.fst ℝ ((Fin (n ^ 2 - 1) → ℝ)) ℝ) +
    (ContinuousLinearMap.snd ℝ ((Fin (n ^ 2 - 1) → ℝ)) ℝ).smulRight (normal (immersion x))
private lemma fullFrame_apply {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (v : (Fin (n ^ 2 - 1) → ℝ) × ℝ) :
    fullFrame x v = fderiv ℝ immersion x v.1 + v.2 • normal (immersion x) := rfl
private lemma fullFrame_injective {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    Function.Injective (fullFrame x) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change fullFrame x v = 0 at hv
  have hroot : (immersion x).val.PosDef := root_posdef (rhoH x) (by rwa [rhoH_val])
  have hS := S4_pos hn (immersion x) hroot
  have hinner := congrArg (normalFunctional (immersion x)) hv
  rw [fullFrame_apply,map_add,map_smul,normalFunctional_apply,
    immersion_normal_tangent hn x hx,normalFunctional_apply,normal_unit _ hS] at hinner
  have ht : v.2 = 0 := by simpa using hinner
  rw [fullFrame_apply,ht,zero_smul,add_zero] at hv
  have hv1 : v.1 = 0 := (immersion_derivative_injective hn x hx) (hv.trans (map_zero _).symm)
  exact Prod.ext hv1 ht
private lemma fullFrame_finrank {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ ((Fin (n ^ 2 - 1) → ℝ) × ℝ) = Module.finrank ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) := by
  have hH := (readoutEquiv n).finrank_eq
  have hdim : Module.finrank ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) = n^2 := by
    rw [hH]
    simp [Module.finrank_pi]
    ring
  rw [hdim]
  simp only [Module.finrank_prod,Module.finrank_self]
  have hc : Module.finrank ℝ ((Fin (n ^ 2 - 1) → ℝ)) = n^2-1 := by simp [Module.finrank_pi]
  rw [hc]
  have hn2 : 1 ≤ n^2 := by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.ne_of_gt hn))
  omega
private def fullFrameEquiv {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    ((Fin (n ^ 2 - 1) → ℝ) × ℝ) ≃L[ℝ] (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (LinearMap.linearEquivOfInjective (fullFrame x).toLinearMap
    (fullFrame_injective hn x hx) (fullFrame_finrank hn)).toContinuousLinearEquiv
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
private def de {n : ℕ} (i j : (Fin (n^2-1))) (x : (Fin (n ^ 2 - 1) → ℝ)) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  fderiv ℝ (tangentFrame i) x (Pi.single j 1)
private def secondForm {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (i j : (Fin (n^2-1))) : ℝ :=
  hermBilinear n ((fun y => normal (immersion y)) x) (de i j x)
private lemma B_symm {n : ℕ} (V W : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) : hermBilinear n V W = hermBilinear n W V :=
  herm_inner_symm _ _
private lemma B_smooth {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (x : E)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => hermBilinear n (f t) (g t)) x := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun V : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) => V.val) := ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).subtypeL.contDiff
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Matrix (Fin n) (Fin n) ℂ) × (Matrix (Fin n) (Fin n) ℂ) => (LinearMap.mul ℝ (A := Matrix (Fin n) (Fin n) ℂ)).toContinuousBilinearMap p.1 p.2) :=
    ((LinearMap.mul ℝ (A := Matrix (Fin n) (Fin n) ℂ)).toContinuousBilinearMap).isBoundedBilinearMap.contDiff
  exact ((Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap)).contDiff.contDiffAt.comp x
    (hm.contDiffAt.comp x ((hv.contDiffAt.comp x hf).prodMk (hv.contDiffAt.comp x hg)))
private lemma B_fderiv {n : ℕ} (f g : (Fin (n ^ 2 - 1) → ℝ) → (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (x v : (Fin (n ^ 2 - 1) → ℝ))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun t => hermBilinear n (f t) (g t)) x v =
      hermBilinear n (f x) (fderiv ℝ g x v) + hermBilinear n (fderiv ℝ f x v) (g x) := by
  rw [(hermBilinear n).fderiv_of_bilinear hf hg]
  rfl
private lemma frame_smooth {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tangentFrame i) x := by
  exact ((immersion_contDiffAt x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
private lemma de_smooth {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (de i j) x := by
  exact ((frame_smooth x hx i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
private lemma N_smooth {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => normal (immersion y)) x := by
  have hroot : (immersion x).val.PosDef := root_posdef (rhoH x) (by rwa [rhoH_val])
  exact (normal_contDiffAt _ (S4_pos hn _ hroot)).comp x (immersion_contDiffAt x hx)
private lemma b_smooth {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => secondForm t i j) x :=
  B_smooth (fun y => normal (immersion y)) (de i j) x (N_smooth hn x hx) (de_smooth x hx i j)
private lemma metric_entry_smooth {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => rootMetric t i j) x :=
  B_smooth (tangentFrame i) (tangentFrame j) x (frame_smooth x hx i) (frame_smooth x hx j)
private lemma frame_second {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    de i j x = fderiv ℝ (fderiv ℝ immersion) x (Pi.single j 1) (Pi.single i 1) := by
  unfold de tangentFrame
  rw [fderiv_clm_apply ((immersion_contDiffAt x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp) |>.differentiableAt (by simp))
    (differentiableAt_const _)]
  simp
private lemma de_symm {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    de i j x = de j i x := by
  rw [frame_second x hx i j,frame_second x hx j i]
  exact (immersion_contDiffAt x hx).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) _ _
private lemma de_mixed {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j k : (Fin (n^2-1))) :
    fderiv ℝ (de i j) x (Pi.single k 1) = fderiv ℝ (de i k) x (Pi.single j 1) := by
  unfold de
  rw [fderiv_clm_apply ((frame_smooth x hx i).fderiv_right (m := (⊤ : ℕ∞)) (by simp) |>.differentiableAt (by simp)) (differentiableAt_const _),
    fderiv_clm_apply ((frame_smooth x hx i).fderiv_right (m := (⊤ : ℕ∞)) (by simp) |>.differentiableAt (by simp)) (differentiableAt_const _)]
  simpa using (frame_smooth x hx i).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) (Pi.single k 1) (Pi.single j 1)
private lemma N_unit {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    hermBilinear n ((fun y => normal (immersion y)) x) ((fun y => normal (immersion y)) x) = 1 := by
  exact normal_unit _ (S4_pos hn _ (root_posdef (rhoH x) (by rwa [rhoH_val])))
private lemma N_orthogonal {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i : (Fin (n^2-1))) :
    hermBilinear n ((fun y => normal (immersion y)) x) (tangentFrame i x) = 0 :=
  immersion_normal_tangent hn x hx _
private lemma DN_orthogonal {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    hermBilinear n ((fun y => normal (immersion y)) x) (fderiv ℝ (fun y => normal (immersion y)) x v) = 0 := by
  have he : (fun t => hermBilinear n ((fun y => normal (immersion y)) t) ((fun y => normal (immersion y)) t)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact N_unit hn t ht
  have hh := congrArg (fun L : (Fin (n ^ 2 - 1) → ℝ) →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
  rw [B_fderiv (fun y => normal (immersion y)) (fun y => normal (immersion y)) x v ((N_smooth hn x hx).differentiableAt (by simp))
    ((N_smooth hn x hx).differentiableAt (by simp))] at hh
  rw [B_symm (fderiv ℝ (fun y => normal (immersion y)) x v) ((fun y => normal (immersion y)) x)] at hh
  have hc : fderiv ℝ (fun _ : (Fin (n ^ 2 - 1) → ℝ) => (1 : ℝ)) x v = 0 := by simp
  rw [hc] at hh
  linarith
private lemma DN_frame {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    hermBilinear n (tangentFrame i x) (fderiv ℝ (fun y => normal (immersion y)) x (Pi.single j 1)) = - secondForm x i j := by
  have he : (fun t => hermBilinear n ((fun y => normal (immersion y)) t) (tangentFrame i t)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact N_orthogonal hn t ht i
  have hh := congrArg (fun L : (Fin (n ^ 2 - 1) → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) (he.fderiv_eq (𝕜 := ℝ))
  rw [B_fderiv (fun y => normal (immersion y)) (tangentFrame i) x _ ((N_smooth hn x hx).differentiableAt (by simp))
    ((frame_smooth x hx i).differentiableAt (by simp))] at hh
  rw [B_symm (fderiv ℝ (fun y => normal (immersion y)) x (Pi.single j 1)) (tangentFrame i x)] at hh
  have hc : fderiv ℝ (fun _ : (Fin (n ^ 2 - 1) → ℝ) => (0 : ℝ)) x (Pi.single j 1) = 0 := by simp
  rw [hc] at hh
  change secondForm x i j + _ = 0 at hh
  linarith
private lemma christoffel_frame {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k i j : (Fin (n^2-1))) :
    D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.christoffel rootMetric x k i j =
      ∑ l, (rootMetric x)⁻¹ k l * hermBilinear n (tangentFrame l x) (de i j x) := by
  unfold D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.christoffel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change (1/2 : ℝ) * ((rootMetric x)⁻¹ k l *
    (fderiv ℝ (fun t => hermBilinear n (tangentFrame l t) (tangentFrame j t)) x (Pi.single i 1) +
    fderiv ℝ (fun t => hermBilinear n (tangentFrame l t) (tangentFrame i t)) x (Pi.single j 1) -
    fderiv ℝ (fun t => hermBilinear n (tangentFrame i t) (tangentFrame j t)) x (Pi.single l 1))) = _
  rw [B_fderiv _ _ x _ ((frame_smooth x hx l).differentiableAt (by simp)) ((frame_smooth x hx j).differentiableAt (by simp)),
    B_fderiv _ _ x _ ((frame_smooth x hx l).differentiableAt (by simp)) ((frame_smooth x hx i).differentiableAt (by simp)),
    B_fderiv _ _ x _ ((frame_smooth x hx i).differentiableAt (by simp)) ((frame_smooth x hx j).differentiableAt (by simp))]
  change _ * ( _ * (hermBilinear n (tangentFrame l x) (de j i x) + hermBilinear n (de l i x) (tangentFrame j x) +
    (hermBilinear n (tangentFrame l x) (de i j x) + hermBilinear n (de l j x) (tangentFrame i x)) -
    (hermBilinear n (tangentFrame i x) (de j l x) + hermBilinear n (de i l x) (tangentFrame j x)))) = _
  rw [de_symm x hx j i,de_symm x hx l i,de_symm x hx l j,B_symm (de j l x) (tangentFrame i x)]
  ring
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
private def dual {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (k : (Fin (n^2-1))) : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) →L[ℝ] ℝ :=
  ∑ l, (rootMetric x)⁻¹ k l • hermBilinear n (tangentFrame l x)
private lemma dual_apply {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (k : (Fin (n^2-1))) (V : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :
    dual x k V = ∑ l, (rootMetric x)⁻¹ k l * hermBilinear n (tangentFrame l x) V := by
  simp [dual]
private lemma metric_isUnit {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    IsUnit (rootMetric x).det := isUnit_iff_ne_zero.mpr (ne_of_gt (rootMetric_posdef hn x hx).det_pos)
private lemma metric_symmetric {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) : (rootMetric x).IsSymm := by
  ext i j
  exact B_symm _ _
private lemma dual_frame {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k i : (Fin (n^2-1))) :
    dual x k (tangentFrame i x) = if k=i then 1 else 0 := by
  rw [dual_apply]
  change (∑ l, (rootMetric x)⁻¹ k l * rootMetric x l i) = _
  have hh := congrArg (fun A : Matrix ((Fin (n^2-1))) ((Fin (n^2-1))) ℝ => A k i)
    (Matrix.nonsing_inv_mul (rootMetric x) (metric_isUnit hn x hx))
  simpa only [Matrix.mul_apply,Matrix.one_apply] using hh
private lemma dual_N {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k : (Fin (n^2-1))) :
    dual x k ((fun y => normal (immersion y)) x) = 0 := by
  rw [dual_apply]
  have hh (l : (Fin (n^2-1))) : hermBilinear n (tangentFrame l x) ((fun y => normal (immersion y)) x) = 0 :=
    (B_symm _ _).trans (N_orthogonal hn x hx l)
  simp_rw [hh]
  simp
private lemma immersion_derivative_expansion {n : ℕ} (x v : (Fin (n ^ 2 - 1) → ℝ)) :
    fderiv ℝ immersion x v = ∑ i, v i • tangentFrame i x := by
  have he : (∑ i : (Fin (n^2-1)), v i • Pi.single i (1 : ℝ)) = v := by
    ext k
    simp [Pi.single_apply,Finset.sum_apply]
  conv_lhs => rw [← he]
  rw [map_sum]
  simp only [map_smul,tangentFrame]
private lemma dual_derivative {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k : (Fin (n^2-1))) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    dual x k (fderiv ℝ immersion x v) = v k := by
  rw [immersion_derivative_expansion,map_sum]
  simp [map_smul,dual_frame hn x hx]
private lemma frame_decomposition {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (V : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :
    V = (∑ k, dual x k V • tangentFrame k x) + hermBilinear n ((fun y => normal (immersion y)) x) V • (fun y => normal (immersion y)) x := by
  obtain ⟨v,hv⟩ := (fullFrameEquiv hn x hx).surjective V
  change fullFrame x v = V at hv
  subst V
  rw [fullFrame_apply]
  change fderiv ℝ immersion x v.1 + v.2 • (fun y => normal (immersion y)) x =
    (∑ k, dual x k (fderiv ℝ immersion x v.1 + v.2 • (fun y => normal (immersion y)) x) • tangentFrame k x) +
    hermBilinear n ((fun y => normal (immersion y)) x) (fderiv ℝ immersion x v.1 + v.2 • (fun y => normal (immersion y)) x) • (fun y => normal (immersion y)) x
  have hd : ∀ k, dual x k (fderiv ℝ immersion x v.1 + v.2 • (fun y => normal (immersion y)) x) = v.1 k := by
    intro k
    rw [map_add,map_smul,dual_derivative hn x hx,dual_N hn x hx]
    simp
  simp_rw [hd]
  have hN : hermBilinear n ((fun y => normal (immersion y)) x) (fderiv ℝ immersion x v.1 + v.2 • (fun y => normal (immersion y)) x) = v.2 := by
    rw [map_add,map_smul]
    have hz : hermBilinear n ((fun y => normal (immersion y)) x) (fderiv ℝ immersion x v.1) = 0 := immersion_normal_tangent hn x hx _
    rw [hz,N_unit hn x hx]
    simp
  rw [hN,immersion_derivative_expansion]
private lemma inverse_metric_smooth {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => (rootMetric t)⁻¹ i j) x :=
  D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.inverse_entry_contDiffAt rootMetric x (metric_entry_smooth x hx)
    (isUnit_iff_ne_zero.mp (metric_isUnit hn x hx)) i j
private lemma christoffel_smooth {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k i j : (Fin (n^2-1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t => D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.christoffel rootMetric t k i j) x := by
  have he : (fun t => D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.christoffel rootMetric t k i j) =ᶠ[𝓝 x]
    (fun t => ∑ l, (rootMetric t)⁻¹ k l * hermBilinear n (tangentFrame l t) (de i j t)) := by
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact christoffel_frame t ht k i j
  apply ContDiffAt.congr_of_eventuallyEq _ he
  apply ContDiffAt.sum
  intro l _
  exact (inverse_metric_smooth hn x hx k l).mul
    (B_smooth _ _ x (frame_smooth x hx l) (de_smooth x hx i j))
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
private lemma frame_structure {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    de i j x = structureRHS tangentFrame (fun y => normal (immersion y)) (D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.christoffel rootMetric) secondForm i j x := by
  rw [frame_decomposition hn x hx (de i j x)]
  unfold structureRHS secondForm
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [christoffel_frame x hx,dual_apply]
private lemma b_symm {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    secondForm x i j = secondForm x j i := by
  unfold secondForm
  rw [de_symm x hx]
private lemma DN_dual {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k j : (Fin (n^2-1))) :
    dual x k (fderiv ℝ (fun y => normal (immersion y)) x (Pi.single j 1)) = -∑ l, (rootMetric x)⁻¹ k l * Matrix.of (secondForm x) j l := by
  rw [dual_apply]
  simp_rw [DN_frame hn x hx,← b_symm x hx j]
  simp [Finset.sum_neg_distrib]
private lemma coordinate_ricci {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (i j : (Fin (n^2-1))) :
    D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.ricci rootMetric x i j =
      secondForm x i j * (∑ k, ∑ l, (rootMetric x)⁻¹ k l * Matrix.of (secondForm x) k l) -
      ∑ k, ∑ l, secondForm x i k * (rootMetric x)⁻¹ k l * Matrix.of (secondForm x) j l := by
  apply ricci_of_structure rootMetric tangentFrame (fun y => normal (immersion y)) secondForm x (dual x)
  · intro l; exact (frame_smooth x hx l).differentiableAt (by simp)
  · exact (N_smooth hn x hx).differentiableAt (by simp)
  · intro l i j; exact (christoffel_smooth hn x hx l i j).differentiableAt (by simp)
  · intro i j; exact (b_smooth hn x hx i j).differentiableAt (by simp)
  · exact dual_frame hn x hx
  · exact dual_N hn x hx
  · intro i j
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact frame_structure hn t ht i j
  · exact de_mixed x hx
  · intro k i j; rw [christoffel_frame x hx,christoffel_frame x hx,de_symm x hx]
  · exact DN_dual hn x hx
private lemma ricci_matrix_gauss {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    (Matrix.of (fun i j => ricci rootMetric x i j)) = ((rootMetric x)⁻¹ * Matrix.of (secondForm x)).trace • Matrix.of (secondForm x) -
      Matrix.of (secondForm x) * (rootMetric x)⁻¹ * Matrix.of (secondForm x) := by
  ext i j
  simp only [Matrix.of_apply]
  rw [coordinate_ricci hn x hx]
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.of_apply]
  simp_rw [Finset.sum_mul]
  have ht : (∑ k : (Fin (n^2-1)), ∑ l : (Fin (n^2-1)), (rootMetric x)⁻¹ k l * secondForm x k l) =
      ∑ k : (Fin (n^2-1)), ∑ l : (Fin (n^2-1)), (rootMetric x)⁻¹ k l * secondForm x l k := by
    simp_rw [b_symm x hx]
  rw [ht,Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  ·
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [b_symm x hx j k]
private lemma coordinate_gauss_scalar {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.scalarCurvature rootMetric x =
      ((rootMetric x)⁻¹ * Matrix.of (secondForm x)).trace^2 - (((rootMetric x)⁻¹ * Matrix.of (secondForm x))^2).trace :=
  coordinate_gauss_scalar_of_ricci rootMetric x (secondForm x) (metric_symmetric x)
    (ricci_matrix_gauss hn x hx)
set_option backward.isDefEq.respectTransparency false
private lemma jordan_normal_val {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :
    (jordan Y (normal Y)).val = (2*(Real.sqrt (S4 Y))⁻¹) • Y.val^3 := by
  rw [jordan_val,normal_val]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  have h1 : Y.val*Y.val^2 = Y.val^3 := by noncomm_ring
  have h2 : Y.val^2*Y.val = Y.val^3 := by noncomm_ring
  rw [h1,h2]
  module
private lemma jordan_square_normal_val {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :
    (jordan Y (jordan Y (normal Y))).val = (4*(Real.sqrt (S4 Y))⁻¹) • Y.val^4 := by
  rw [jordan_val,jordan_normal_val]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  have h1 : Y.val*Y.val^3 = Y.val^4 := by noncomm_ring
  have h2 : Y.val^3*Y.val = Y.val^4 := by noncomm_ring
  rw [h1,h2]
  module
private lemma inner_normal_jordan_normal {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hS : 0 < S4 Y) :
    herm_inner (normal Y).val (jordan Y (normal Y)).val =
      2*(Y.val^5).trace.re/S4 Y := by
  rw [jordan_normal_val,normal_val,herm_inner_smul_left,herm_inner_smul_right]
  have hp : herm_inner (Y.val^2) (Y.val^3) = (Y.val^5).trace.re := by
    change (Y.val^2*Y.val^3).trace.re = _
    rw [← pow_add]
  rw [hp]
  have hs := Real.sq_sqrt hS.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hS)
  field_simp
  rw [hs]
  ring
private lemma inner_normal_jordan_square_normal {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hS : 0 < S4 Y) :
    herm_inner (normal Y).val (jordan Y (jordan Y (normal Y))).val =
      4*(Y.val^6).trace.re/S4 Y := by
  rw [jordan_square_normal_val,normal_val,herm_inner_smul_left,herm_inner_smul_right]
  have hp : herm_inner (Y.val^2) (Y.val^4) = (Y.val^6).trace.re := by
    change (Y.val^2*Y.val^4).trace.re = _
    rw [← pow_add]
  rw [hp]
  have hs := Real.sq_sqrt hS.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hS)
  field_simp
  rw [hs]
  ring
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
private def shape {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) : Module.End ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) :=
  (Real.sqrt (S4 Y))⁻¹ •
    (D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.Traces.RankOne.rankOneProjection (normalFunctional Y).toLinearMap (normal Y) *
      (jordan Y).toLinearMap *
      D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.Traces.RankOne.rankOneProjection (normalFunctional Y).toLinearMap (normal Y))
private lemma shape_gauss_spectral {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hS : 0 < S4 Y) :
    (LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (shape Y))^2 - LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) ((shape Y)^2) =
      9*D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio Y.property.isHermitian.eigenvalues := by
  have hu : (normalFunctional Y).toLinearMap (normal Y) = 1 := normal_unit Y hS
  have ht := D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.Traces.RankOne.gauss_trace_rank_one_contraction
    (normalFunctional Y).toLinearMap (normal Y) hu (jordan Y).toLinearMap
      (Real.sqrt (S4 Y)) (ne_of_gt (Real.sqrt_pos.mpr hS))
  change (LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (shape Y))^2 - LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) ((shape Y)^2) = _ at ht
  rw [ht,(hermitian_jordan_operator_trace_formulas Y).1,
    (hermitian_jordan_operator_trace_formulas Y).2]
  change ((2*n*∑ i, Y.property.isHermitian.eigenvalues i)^2 -
    (2*n*(∑ i, Y.property.isHermitian.eigenvalues i^2)+2*(∑ i, Y.property.isHermitian.eigenvalues i)^2) -
    2*(2*n*∑ i, Y.property.isHermitian.eigenvalues i)*herm_inner (normal Y).val (jordan Y (normal Y)).val +
      2*herm_inner (normal Y).val (jordan Y (jordan Y (normal Y))).val)/(Real.sqrt (S4 Y))^2 = _
  rw [inner_normal_jordan_normal Y hS,inner_normal_jordan_square_normal Y hS,Real.sq_sqrt hS.le]
  simp_rw [trace_pow_eq_eigenvalues]
  unfold D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralN
  simp_rw [P_evalSum]
  simp only [pow_one]
  have h4 := ne_of_gt hS
  rw [S4_eq_sum] at h4 ⊢
  field_simp
  <;> ring
private def shapeMatrix {n : ℕ} (x : (Fin (n ^ 2 - 1) → ℝ)) : Matrix ((Fin (n^2-1))) ((Fin (n^2-1))) ℝ :=
  - ((rootMetric x)⁻¹ * Matrix.of (secondForm x))
private lemma shape_apply {n : ℕ} (Y V : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) : shape Y V =
    (Real.sqrt (S4 Y))⁻¹ • D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection Y
      (jordan Y (D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection Y V)) := rfl
private lemma shape_normal {n : ℕ} (Y : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hS : 0 < S4 Y) : shape Y (normal Y) = 0 := by
  have hp : D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection Y (normal Y) = 0 := by
    unfold D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection
    rw [normal_unit Y hS]
    simp
  rw [shape_apply,hp,map_zero]
  simp [D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection,herm_inner]
private lemma DN_shape_derivative {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    shape (immersion x) (fderiv ℝ immersion x v) = fderiv ℝ (fun y => normal (immersion y)) x v := by
  have hS := S4_pos hn (immersion x) (root_posdef (rhoH x) (by rwa [rhoH_val]))
  have ht : D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection (immersion x) (fderiv ℝ immersion x v) =
      fderiv ℝ immersion x v := by
    unfold D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative.projection
    rw [immersion_normal_tangent hn x hx,zero_smul,sub_zero]
  rw [shape_apply,ht,← regular_level_set_shape_operator _ _ hS]
  change _ = fderiv ℝ (normal ∘ immersion) x v
  rw [fderiv_comp x ((normal_contDiffAt _ hS).differentiableAt (by simp))
    ((immersion_contDiffAt x hx).differentiableAt (by simp))]
  rfl
private lemma pi_derivative_expansion {n : ℕ} (L : (Fin (n ^ 2 - 1) → ℝ) →L[ℝ] (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    L v = ∑ j : (Fin (n^2-1)), v j • L (Pi.single j 1) := by
  have he : (∑ j : (Fin (n^2-1)), v j • Pi.single j (1 : ℝ)) = v := by
    ext k
    simp [Pi.single_apply,Finset.sum_apply]
  conv_lhs => rw [← he]
  rw [map_sum]
  simp only [map_smul]
private lemma DN_dual_vector {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (k : (Fin (n^2-1))) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    dual x k (fderiv ℝ (fun y => normal (immersion y)) x v) = (shapeMatrix x).toLin' v k := by
  rw [pi_derivative_expansion,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp_rw [DN_dual hn x hx]
  change (∑ j : (Fin (n^2-1)), v j * (-∑ l : (Fin (n^2-1)), (rootMetric x)⁻¹ k l * Matrix.of (secondForm x) j l)) =
    ∑ j : (Fin (n^2-1)), (-(∑ l : (Fin (n^2-1)), (rootMetric x)⁻¹ k l * Matrix.of (secondForm x) l j)) * v j
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.of_apply]
  rw [b_symm x hx]
private lemma DN_fullFrame {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) (v : (Fin (n ^ 2 - 1) → ℝ)) :
    fderiv ℝ (fun y => normal (immersion y)) x v = fullFrame x ((shapeMatrix x).toLin' v,0) := by
  rw [frame_decomposition hn x hx (fderiv ℝ (fun y => normal (immersion y)) x v),DN_orthogonal hn x hx,
    zero_smul,add_zero,fullFrame_apply,zero_smul,add_zero,immersion_derivative_expansion]
  simp_rw [DN_dual_vector hn x hx]
private lemma shape_conjugate {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    (fullFrameEquiv hn x hx).symm.toLinearEquiv.conj (shape (immersion x)) =
      ((shapeMatrix x).toLin').prodMap (0 : ℝ →ₗ[ℝ] ℝ) := by
  apply LinearMap.ext
  intro v
  apply (fullFrameEquiv hn x hx).injective
  simp (config := { congrConsts := false }) only [LinearEquiv.conj_apply,LinearMap.comp_apply]
  change (fullFrameEquiv hn x hx) ((fullFrameEquiv hn x hx).symm
    (shape (immersion x) ((fullFrameEquiv hn x hx) v))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change shape (immersion x) (fullFrame x v) = fullFrame x ((shapeMatrix x).toLin' v.1,0)
  have hS : 0 < S4 (immersion x) := S4_pos hn _ (root_posdef (rhoH x) (by rwa [rhoH_val]))
  rw [fullFrame_apply,map_add,map_smul,
    shape_normal (immersion x) hS,smul_zero,add_zero,
    DN_shape_derivative hn x hx,DN_fullFrame hn x hx]
private lemma shape_trace {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (shape (immersion x)) = (shapeMatrix x).trace := by
  rw [← LinearMap.trace_conj' (shape (immersion x)) (fullFrameEquiv hn x hx).symm.toLinearEquiv,
    shape_conjugate hn x hx,LinearMap.trace_prodMap']
  simp
private lemma shape_square_trace {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) ((shape (immersion x))^2) = ((shapeMatrix x)^2).trace := by
  let e := (fullFrameEquiv hn x hx).symm.toLinearEquiv
  have hp : e.conj ((shape (immersion x))^2) =
      (((shapeMatrix x).toLin')^2).prodMap (0 : ℝ →ₗ[ℝ] ℝ) := by
    have he : e.conj ((shape (immersion x))^2) = (e.conj (shape (immersion x)))^2 :=
      e.conjRingEquiv.map_pow _ 2
    rw [he,shape_conjugate hn x hx]
    ext v <;> simp [pow_two,Module.End.mul_apply]
  rw [← LinearMap.trace_conj' _ e,hp,LinearMap.trace_prodMap']
  simp only [map_zero,add_zero,← Matrix.toLin'_pow,Matrix.trace_toLin'_eq]
private lemma coordinate_shape_gauss {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    D5.S3.Geometry.AlphaGeometry.EuclideanHypersurfaceGauss.scalarCurvature rootMetric x =
      (LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (shape (immersion x)))^2 -
        LinearMap.trace ℝ ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) ((shape (immersion x))^2) := by
  rw [coordinate_gauss_scalar hn x hx,shape_trace hn x hx,shape_square_trace hn x hx]
  simp only [shapeMatrix,Matrix.trace_neg,neg_sq,neg_sq]
set_option backward.isDefEq.respectTransparency false
private lemma root_trace_pow {n : ℕ} (A : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hA : A.val.PosDef) (k : ℕ) :
    ((root A).val^k).trace.re = ∑ i, (A.property.isHermitian.eigenvalues i ^ (1/3 : ℝ))^k := by
  let e := Unitary.conjStarAlgAut ℂ ((Matrix (Fin n) (Fin n) ℂ)) A.property.isHermitian.eigenvectorUnitary
  have he : (root A).val = e (Matrix.diagonal fun i => ((A.property.isHermitian.eigenvalues i ^ (1/3 : ℝ) : ℝ) : ℂ)) := by
    change CFC.rpow A.val (1/3 : ℝ) = _
    rw [show CFC.rpow A.val (1/3 : ℝ) = cfc (fun t : ℝ => t ^ (1/3 : ℝ)) A.val from
      CFC.rpow_eq_cfc_real (a := A.val) (y := (1/3 : ℝ)) hA.posSemidef.nonneg,Matrix.IsHermitian.cfc_eq A.property]
    rfl
  conv_lhs => rw [he,← map_pow]
  simp only [e,Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,Matrix.one_mul,Matrix.diagonal_pow,
    Matrix.trace_diagonal,Complex.re_sum,Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.ofReal_pow,Complex.ofReal_re]
private lemma root_moment {n : ℕ} (A : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hA : A.val.PosDef) (k : ℕ) :
    P _ (root A).property.isHermitian.eigenvalues k =
      P _ (fun i => A.property.isHermitian.eigenvalues i ^ (1/3 : ℝ)) k := by
  simp only [P_evalSum]
  exact (trace_pow_eq_eigenvalues (root A) k).symm.trans (root_trace_pow A hA k)
private lemma root_spectral_ratio {n : ℕ} (A : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) (hA : A.val.PosDef) :
    D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio (root A).property.isHermitian.eigenvalues =
      D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.lambdaRatio A.property.isHermitian.eigenvalues := by
  unfold D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.lambdaRatio D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralN
  simp_rw [root_moment A hA]
private lemma density_eig_simplex {n : ℕ} (A : (Matrix (Fin n) (Fin n) ℂ)) (hA : A ∈ densityStates n) :
    eig A ∈ PositiveSimplexGeometryAndMixing.simplex n := by
  have hh := hA.1.isHermitian
  have he : eig A = hh.eigenvalues := dif_pos hh
  rw [he]
  constructor
  · intro i; exact hA.1.eigenvalues_pos i
  · have ht := hh.trace_eq_sum_eigenvalues
    have hr := congrArg Complex.re ht
    rw [hA.2] at hr
    simpa using hr.symm
set_option backward.isDefEq.respectTransparency false
open Filter
private lemma chart_scalar_spectral {n : ℕ} (hn : 0 < n) (x : (Fin (n ^ 2 - 1) → ℝ)) (hx : (rho x).PosDef) :
    scalarCurvature metric x = D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio (immersion x).property.isHermitian.eigenvalues := by
  have he : (@metric n) =ᶠ[𝓝 x] (fun t => (9 : ℝ) • rootMetric t) := by
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact metric_eq_nine_rootMetric t ht
  have hd : ∀ᶠ t in 𝓝 x, IsUnit (rootMetric t).det := by
    filter_upwards [(D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates.positive_chart_open n).mem_nhds hx] with t ht
    exact metric_isUnit hn t ht
  have hS : 0 < S4 (immersion x) := S4_pos hn _ (root_posdef (rhoH x) (by rwa [rhoH_val]))
  change scalarCurvature metric x = _
  rw [scalarCurvature_congr_nhds metric _ x he,scalar_curvature_embedding_dilation_three rootMetric x hd,
    coordinate_shape_gauss hn x hx,
    shape_gauss_spectral (immersion x) hS]
  ring
lemma scal3_eq_spectral_ratio (n : ℕ) (hn : 2 ≤ n) (A : (Matrix (Fin n) (Fin n) ℂ)) (hA : A ∈ densityStates n) :
    scal3 A = D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.lambdaRatio (eig A) := by
  have hpos : 0 < n := by omega
  have hc : rho (chartPoint A) = A := hermitian_trace_one_chart_equiv hpos A hA.1.isHermitian hA.2
  have hx : (rho (chartPoint A)).PosDef := by rw [hc]; exact hA.1
  have he : rhoH (chartPoint A) = (⟨A,hA.1.isHermitian⟩ : (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) := by
    apply Subtype.ext
    rw [rhoH_val,hc]
  unfold scal3
  rw [chart_scalar_spectral hpos _ hx]
  change D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector.spectralRatio (root (rhoH (chartPoint A))).property.isHermitian.eigenvalues = _
  rw [he,root_spectral_ratio _ hA.1]
  have hh : eig A = hA.1.isHermitian.eigenvalues := dif_pos hA.1.isHermitian
  rw [hh]
theorem result : claim := by
  intro n hn A B hA hB hm
  rw [scal3_eq_spectral_ratio n hn A hA,scal3_eq_spectral_ratio n hn B hB]
  exact ⟨spectral_moreMixed_monotone hn (eig B) (eig A)
      (density_eig_simplex B hB) (density_eig_simplex A hA) hm,
    fun hnp => spectral_moreMixed_strict hn (eig B) (eig A)
      (density_eig_simplex B hB) (density_eig_simplex A hA) hm hnp⟩

end D5.S3.Geometry.AlphaGeometry.QuantumCubeRootScalarCurvatureMonotone
