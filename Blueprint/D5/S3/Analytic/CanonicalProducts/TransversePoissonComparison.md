# Transverse Poisson comparison

## Abstract

Integrated logarithmic defects satisfy two-sided Poisson comparisons.

**Theorem 1.1 (The complete two-sided comparison).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/TransversePoissonComparison.integrated_defect_poisson_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/TransversePoissonComparison.integrated_defect_poisson_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary index type I, assume nonnegative real weights w, displacements 0<=a(i)<=1/2, individually positive heights gamma(i), and summability of w(i)*a(i)^2/gamma(i)^2. For every real T>=1, let P(T) be the unordered real sum of w(i)*a(i)^2*T/(T^2+gamma(i)^2). The integratedDefect defined in IntegratedTransverseMoment satisfies (8/9)*P(T)<=integratedDefect(T)<=8*P(T). The constants and threshold are uniform in the family; no finite total weighted second moment or uniform positive lower bound on height is assumed.

Write A=(T+v)^2+gamma^2, B=(T-v)^2+gamma^2 and R=T^2+gamma^2. Positivity of gamma makes all three denominators positive. The real logarithm inequalities 1-1/x<=log(x)<=x-1 applied to A/B give 4*T*v/A<=log(A/B)<=4*T*v/B. On 0<=v<=1/2 and T>=1, the square comparisons yield 4*A<=9*R and R<=4*B. Thus 16*T*v/(9*R)<=log(A/B)<=16*T*v/R. Integrating on [0,a] gives the endpoint comparison with constants 8/9 and 8.

The Poisson terms are nonnegative and bounded by T times the supplied inverse-square summable budget. Multiplying the endpoint bounds by the nonnegative weights gives two summable families. The proof consumes the exact endpoint-sum identity from integrated_transverse_moment and compares the unordered real sums. This is a substantive scalar estimate and integral argument, followed by summation; it does not duplicate the integrated moment theorem or add a counting wrapper.

The empty family, zero weights, zero displacements, a=1/2 and T=1 are included. Heights may be arbitrarily small but must remain positive at each index. The total weighted second moment may be infinite in the extended nonnegative reals; the inverse-square budget and the fixed-T Poisson sum are different quantities. These are abstract analytic functions: identifying them with actual zeta data, establishing the required arithmetic or analytic bounds, and any RH conclusion remain outside this result. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Analytic/CanonicalProducts/TransversePoissonComparison.integrated_defect_poisson_bounds`
- Dependency: [D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment](IntegratedTransverseMoment.md)
