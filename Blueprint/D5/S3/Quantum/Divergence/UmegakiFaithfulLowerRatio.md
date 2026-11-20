# Faithful density pairs from a rare reference flag

## Abstract

Actual faithful flagged density pairs approximate the inverse-weighted channel ratio.

**Theorem 1.1 (Approximation by actual canonical density states).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio.faithful_density_pair_ratio_approx`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio.faithful_density_pair_ratio_approx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a finite completely positive trace-preserving channel from A to B with N(I_A) positive definite. Let R be any finite reference, Z a positive definite complex matrix on R times A, and V any complex matrix on that same joint space with partialTraceRight V equal to zero. Put T equal to the canonical referenceAction on R. Suppose qin=Re Tr(V dagger Z inverse V) is strictly positive, and put qout=Re Tr((TV) dagger (TZ) inverse TV). For every positive real tolerance there exist actual DensityState values rho and sigma on (Fin 2 times R) times A. Both input matrices and both canonical referenceState outputs are positive definite. The input reference marginals agree, and so do the output reference marginals. Both pairs satisfy canonical SupportContained, the canonical finiteTraceLogRelativeEntropy of the input pair is strictly positive, and the absolute difference between the actual output/input divergence ratio and qout/qin is less than the tolerance. The output conditional numerator equals the output divergence because the two actual output reference marginals agree.

The reference flag enlarges the reference system. In sum coordinates the base is diag(Z,delta I), the Hermitian direction is the off-diagonal matrix with blocks V and V dagger, and the common trace is Re Tr(Z)+delta card(R) card(A). The actual density matrices are the base plus epsilon times this direction and the base, each divided by that common trace, with the explicit finite product association. On the output the lower block is delta T(I), equal to delta times I_R tensor N(I_A). No unitality is assumed. Positivity and trace preservation use the original referenceAction_nonneg and referenceAction_trace. A positive spectral floor and the faithful identity image give faithful channel images.

For each fixed positive delta, the actual BKM path identity, the original affine logDeriv continuity on a positive floor, and the original logDeriv_smul yield the second-order trace-log expansion. The real weighted integral tends to half the BKM pairing by a uniform bound on the interval from zero to one. Transport to Fin(card) uses the CFC logarithm and trace under reindexing and the Bochner integral identity reindex_logDeriv from UmegakiBKMPath. The approximation consumes these analytic, reindexing and flag identities.

The original rare_flag_logDeriv_limit is applied separately with lower reference block I at input and T(I) at output. First choose delta between zero and one so that its normalized input BKM coefficient exceeds qin/2 and its coefficient quotient is within half the tolerance. This earns a strictly positive input BKM coefficient. For that fixed delta, choose a nonzero sufficiently small epsilon with a positive actual input divergence and quotient error below half the tolerance. The shared trace normalization and epsilon squared cancel in the ratio. The quotient uses the positive input form as denominator and allows qout to vanish.

This construction serves the Umegaki complete-versus-conditional problem in Hirche, George, Nuradha and Wilde, arXiv:2608.27171v1, Definition 2, Remark 2 and the second bullet of §9. The approximation assumes faithful N(I_A). UmegakiChannelSupportedExtension uses genuine output depolarization to apply it to arbitrary finite channels.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio.faithful_density_pair_ratio_approx`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiBKMPath](UmegakiBKMPath.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](UmegakiRareFlagBKM.md)
