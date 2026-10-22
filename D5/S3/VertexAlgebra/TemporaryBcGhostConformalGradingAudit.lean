import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingActualConformalState
import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingConformalFiniteComparison
import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingFiniteGrading
import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingHomogeneousDecomposition
import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingLowGrades

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true

#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.originalFock
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.originalFock
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.originalL0
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.originalL0
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.siteWeight_nonneg_of_ne_one
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.siteWeight_nonneg_of_ne_one
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_lower_bound
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_lower_bound
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_siteWeight_le
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_siteWeight_le
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_even_index_bound
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_even_index_bound
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_odd_index_bound
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.occupied_odd_index_bound
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.allowedSites
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.allowedSites
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_subset_allowedSites
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_subset_allowedSites
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_mem_powerset
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.energy_mem_powerset
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabels
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabels
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.GradeLabel
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.GradeLabel
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabel_finite
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabel_finite
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabel_fintype
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeLabel_fintype
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.mem_grade_iff
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.mem_grade_iff
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.L_zero_coefficient
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.L_zero_coefficient
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_eq_eigenspace
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_eq_eigenspace
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeEquiv
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeBasis
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeBasis
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeBasis_coe
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.gradeBasis_coe
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_finiteDimensional
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_finiteDimensional
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_finrank
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_finrank
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceGradeEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceGradeEquiv
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceEquiv
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceBasis
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspaceBasis
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_finiteDimensional
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_finiteDimensional
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_finrank
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_finrank
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_eq_bot_of_lt
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.grade_eq_bot_of_lt
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_eq_bot_of_lt
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenspace_eq_bot_of_lt
#check @D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenvalue_integral
#print axioms D5.S3.VertexAlgebra.BcGhostFiniteGrading.eigenvalue_integral
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.gradeProjection
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.gradeProjection
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_coefficient
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_coefficient
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_homogeneous
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_homogeneous
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.gradeSupport
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.gradeSupport
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_eq_zero_outside_gradeSupport
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_eq_zero_outside_gradeSupport
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_ne_zero_iff
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.project_ne_zero_iff
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.finite_reconstruction
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.finite_reconstruction
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.finite_homogeneous_family_unique
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.finite_homogeneous_family_unique
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.HomogeneousDirectSum
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.HomogeneousDirectSum
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.assembly
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.assembly
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.assembly_decomposition
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.assembly_decomposition
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_grade
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_grade
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_assembly
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_assembly
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.homogeneousEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.homogeneousEquiv
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_eq_finite_sum
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.decomposition_eq_finite_sum
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.actualHomogeneousEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.actualHomogeneousEquiv
#check @D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.actual_decomposition_eq_finite_sum
#print axioms D5.S3.VertexAlgebra.BcGhostHomogeneousDecomposition.actual_decomposition_eq_finite_sum
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.minimumLabels
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.minimumLabels
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.zeroLabels
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.zeroLabels
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.mem_minimumLabels_iff
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.mem_minimumLabels_iff
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.mem_zeroLabels_iff
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.mem_zeroLabels_iff
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.minimumLabelEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.minimumLabelEquiv
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.zeroLabelEquiv
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.zeroLabelEquiv
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.minimum_eigenspace_finrank
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.minimum_eigenspace_finrank
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.zero_eigenspace_finrank
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.zero_eigenspace_finrank
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.minimum_state_reconstruction
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.minimum_state_reconstruction
#check @D5.S3.VertexAlgebra.BcGhostLowGrades.zero_state_reconstruction
#print axioms D5.S3.VertexAlgebra.BcGhostLowGrades.zero_state_reconstruction
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.omegaState
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.omegaState
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.basisWord_pair
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.basisWord_pair
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.omega_field_expansion
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.omega_field_expansion
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_modes
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_modes
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_c_modes
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_c_modes
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_boundary
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_boundary
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_same_half_CAR
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_same_half_CAR
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.c_derivative_b_creator
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.c_derivative_b_creator
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_c_annihilator
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_c_annihilator
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_c_creator
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_b_c_creator
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.c_derivative_b_positive_half
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.c_derivative_b_positive_half
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.b_derivative_c_creator
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.b_derivative_c_creator
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_c_b_annihilator
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.derivative_c_b_annihilator
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_odd_modes
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_odd_modes
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.cbWeight
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.cbWeight
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.dbWeight
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.dbWeight
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.dcWeight
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.dcWeight
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius_encloses_cutoff
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius_encloses_cutoff
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius_contains
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.comparisonRadius_contains
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.weighted_pair_support
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.weighted_pair_support
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_C_dB_interval
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_C_dB_interval
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_dB_C_interval
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_dB_C_interval
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_B_dC_interval
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_B_dC_interval
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_C_dB_swap
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.normal_C_dB_swap
#check @D5.S3.VertexAlgebra.BcGhostActualConformalState.conformal_modes
#print axioms D5.S3.VertexAlgebra.BcGhostActualConformalState.conformal_modes
#check @D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.descending_common_interval
#print axioms D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.descending_common_interval
#check @D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.ascending_common_interval
#print axioms D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.ascending_common_interval
#check @D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.split_common_interval
#print axioms D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison.split_common_interval
