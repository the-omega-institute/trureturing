# Canonical Li coefficients from actual zero pairs

## Abstract

Under right-half-plane nonvanishing, the actual square resolvent gives the derivative-normalized Li coefficients as a sum over zero pairs.

**Definition 1.1 (Cayley ratio of an actual zero).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.zeroRatio`

*Formalization.* `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.zeroRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural index i, the ratio is 1 - 1/rho_i, where rho_i is the corresponding nontrivial zeta zero in zetaZeroData.

**Definition 1.2 (Contribution from a positive-ordinate zero).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient`

*Formalization.* `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and i, the value at a positive ordinate is twice the analytic multiplicity times (1 minus the real part of the nth power of the Cayley ratio). It is zero at other indices. On the critical line this is the multiplicity times the squared norm of one minus that power. The unit norm of the Cayley ratio gives the bound by n squared times the first contribution through the geometric telescoping identity.

**Theorem 1.3 (Convergence of the actual pair series).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient_abs_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient_abs_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, the absolute values of the real pair contributions are summable over all natural indices. Restriction of the summable real Li summand to positive ordinates and multiplication by two give the series.

**Definition 1.4 (Actual pair sum).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairSum`

*Formalization.* `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, the pair sum is the sum of the summable pair contributions in degree n.

**Theorem 1.5 (Derivative-normalized coefficient identity).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonicalLiCoefficient_eq_actual_pairSum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonicalLiCoefficient_eq_actual_pairSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, if n is zero or the completed xi function is nonzero on the open right half-plane with real part greater than one half, the derivative-normalized canonical Li coefficient is exactly the actual pair sum. At index zero both sides vanish. Right-half-plane nonvanishing and the functional equation place all zeros on the critical line. The positive-ordinate square resolvent gives the sum of the conjugate pairs of simple fractions for the logarithmic derivative. The Mobius change of variable yields three geometric series per pair. The first pair contribution times polynomially weighted geometric decay dominates the series in both indices on the unit disk. Exchanging these sums and using uniqueness of scalar power series identifies the canonical coefficient.

**Theorem 1.6 (Fixed first-coefficient quadratic bound).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonical_li_forward_fixed_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonical_li_forward_fixed_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural n, under the same alternative of index zero or right-half-plane nonvanishing, the canonical coefficient lies in the closed interval from zero to the actual first canonical coefficient times n squared. This follows by summing the pointwise squared-norm bounds and using the coefficient identity at n and at one.

**Theorem 1.7 (Canonical Li nonnegativity criterion).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard Riemann hypothesis holds exactly when the canonical Li coefficient is nonnegative at every natural index. The reverse direction uses the positive-index canonical Li criterion.

**Theorem 1.8 (Canonical Li criterion with fixed quadratic bound).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_fixed_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_fixed_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard Riemann hypothesis holds exactly when for every natural n the canonical Li coefficient lies between zero and the first coefficient times n squared, inclusive. The reverse direction uses the canonical quadratic growth criterion.

## References

- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonicalLiCoefficient_eq_actual_pairSum`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.canonical_li_forward_fixed_quadratic`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairCoefficient_abs_summable`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.pairSum`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_fixed_quadratic`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_nonnegative`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent.zeroRatio`
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](AnalyticLogarithmicContinuation.md)
- Dependency: [D5/S3/Weil/Probability/CanonicalLiDiskEquivalence](CanonicalLiDiskEquivalence.md)
- Dependency: [D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse](CanonicalLiNonnegativeConverse.md)
- Dependency: [D5/S3/Weil/ZeroData/LiZeroSumConvergence](../ZeroData/LiZeroSumConvergence.md)
- Dependency: [D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData](../ZeroData/UnconditionalCanonicalZeroData.md)
- Dependency: [D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder](../../Zeros/Resolvent/XiSquareExteriorRemainder.md)
