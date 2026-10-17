import D5.S3.Analytic.Convexity.CFMPTransientPotentialRecovery
import D5.S3.Analytic.Convexity.CFMPTransientPotentialRecoverySanity

/-!
Transient queries for a later, separately governed validation session.
This file has not been run. The import names deliberately refer to the temporary
files in this directory, including the exact supplied local Legendre source.
-/

#check @D5.S3.Analytic.Convexity.MonotoneLegendrePullback.hasFDerivAt_legendre_pullback_of_monotone
#check @hasStrictFDerivAt_norm_sq
#check @HasFDerivAt.const_mul
#check @HasFDerivAt.sub
#check @ContinuousWithinAt.continuousAt
#check @IsOpen.mem_nhds
#check @HasFDerivAt.comp_hasDerivAt
#check @HasDerivAt.smul_const
#check @HasDerivAt.const_add
#check @nonneg_of_mul_nonneg_right
#check @MonotoneOn.convexOn_of_deriv
#check @innerSL_apply_apply
#check @real_inner_smul_right
#check @intervalIntegral.integral_hasDerivAt_right
#check @Continuous.intervalIntegrable
#check @MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
#check @hasFDerivAt_iff_hasDerivAt
#check @not_differentiableAt_abs_zero
#check @finrank_euclideanSpace_fin
#check @TransientPotentialRecovery.T
#check @TransientPotentialRecovery.Omega
#check @TransientPotentialRecovery.P
#check @TransientPotentialRecovery.recover
#check @TransientPotentialRecovery.Sanity.relu
#check @TransientPotentialRecovery.Sanity.reluInverse
#check @TransientPotentialRecovery.Sanity.reluQ
#check @TransientPotentialRecovery.Sanity.relu_recovery
#check @TransientPotentialRecovery.Sanity.relu_not_differentiableAt_zero
