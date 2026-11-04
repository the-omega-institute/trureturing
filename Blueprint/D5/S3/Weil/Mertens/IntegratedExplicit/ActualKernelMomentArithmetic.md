# Original full-kernel certificate source

## Abstract

The complete actual-K moment certificate.

**Theorem 1.1 (B ge C).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.B_ge_C`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.B_ge_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal B=C(1+10!(2/alpha)^10) is at least C; positivity of the factorial term and C>=1 pay this scalar fact.

**Theorem 1.2 (F eq Ioc).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.F_eq_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.F_eq_Ioc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inclusive F(t) sum on Icc(2,floor(exp t)) equals the original Ioc(0,floor(exp t)) sum because the only extra index is 1 and Lambda(1)=0.

**Theorem 1.3 (relativeError le).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.relativeError_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.relativeError_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual global MediumPNT error is at most C on every nonnegative t, using exp(-alpha t^(1/10))<=1.

**Theorem 1.4 (b bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.b_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.b_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual inclusive F, abs(F(t)-t+gamma)<=B for every t>=0. The interval below log 2 has an empty sum. The complete Chebyshev tail identity, retained weighted tail helper, logarithmic substitution and Gamma integral pay the entire tail with exactly B.

**Theorem 1.5 (g pos).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.g_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.g_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual weight g_D(u)=exp(u/2)+exp((D-u)/2) is positive for every real D,u.

**Theorem 1.6 (weight eq sqrt).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weight_eq_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weight_eq_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=2, Lambda(n)exp(-log(n)/2)=Lambda(n)/sqrt(n), by the positive real square root and exp(log n)=n.

**Theorem 1.7 (log cut iff).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.log_cut_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.log_cut_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal logarithmic entry log(n)<=t is equivalent to n<=floor(exp t) for n>=2, including equality.

**Theorem 1.8 (indices).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.indices`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering the original inclusive primes(D) by log(n)<=t gives primes(t) whenever t<=D, without deleting cutoff entries.

**Theorem 1.9 (cumulative).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.cumulative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.cumulative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete sum of Lambda(n) on Icc(2,floor(exp t)) equals the actual inclusive psi(exp t). Prime powers are retained.

**Theorem 1.10 (weighted complex pair).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weighted_complex_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weighted_complex_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part of an arbitrary complex pair is bounded by the two reciprocal positive-weight square terms. This elementary square inequality is consumed by the actual prime and continuum realizations.

**Theorem 1.11 (prefix support).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.prefix_support`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.prefix_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero total mass and nodes in [0,D] make the actual inclusive finite prefix zero outside [0,D]. No node ordering, distinctness or nonempty condition occurs.

**Theorem 1.12 (actual weighted mangoldt translation bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.actual_weighted_mangoldt_translation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.actual_weighted_mangoldt_translation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex atoms in [0,D] of zero mass, the COMPLETE prime quadratic 2 sum Lambda(n)/sqrt(n) c(log n) is at most beta_D E. The actual row is exp(u/2)(psi(exp(D-u))+F(u))+exp((D-u)/2)(psi(exp u)+F(D-u)). The relative psi errors are split at D/4 and 3D/4, and F(t)<=t+B pays the remaining marginals. The weighted pair inequality is integrated and the reverse density translated before summing; no operator, arithmetic or correlation bridge is a premise.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.B_ge_C`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.F_eq_Ioc`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.actual_weighted_mangoldt_translation_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.b_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.cumulative`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.g_pos`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.indices`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.log_cut_iff`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.prefix_support`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.relativeError_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weight_eq_sqrt`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic.weighted_complex_pair`
- Dependency: [D5/S3/Analytic/Interpolation/MomentExponentialCoercivity](../../../Analytic/Interpolation/MomentExponentialCoercivity.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation](ActualKernelPrefixPerturbation.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedMangoldtRate](../WeightedMangoldtRate.md)
