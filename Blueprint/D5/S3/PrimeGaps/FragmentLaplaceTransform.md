# Laplace Transform of the Fragment Law

## Abstract

Derive the Laplace functional of the weighted Poisson fragment law and the real Laplace transform of its total mass.

**Theorem 1.1 (Factor the exponential of a finite sum).**

Lean statement: `D5/S3/PrimeGaps/FragmentLaplaceTransform.exp_neg_ennreal_sum`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentLaplaceTransform.exp_neg_ennreal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index set and extended nonnegative real values, the extended-real exponential of the negative sum equals the product of the exponentials of the negative summands. Finite-set induction proves the identity, including infinite summands, using additivity of the exponential.

**Theorem 1.2 (Laplace functional of a finite Poisson law).**

Lean statement: `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_finitePoissonLaw`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_finitePoissonLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite intensity measure on the real line and any measurable extended nonnegative test function h, the expected exponential of minus the integral of h against the sampled weighted measure equals the exponential of minus the intensity integral of one minus exp(-ofReal(u) h(u)). Conditioning on the Poisson count factors the sampled-location integral into a power; summing those powers with the Poisson weights gives the formula.

**Theorem 1.3 (Laplace functional of the complete fragment law).**

Lean statement: `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_fragmentLaw`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_fragmentLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real cutoff zeta and measurable extended nonnegative test function h, the Laplace functional of fragmentLaw(zeta) is the exponential of minus the integral of one minus exp(-ofReal(u) h(u)) against reciprocal-location intensity on (0,zeta]. Independence gives the formula for finite sets of dyadic bands, and dominated convergence passes to their countable sum. Almost-sure finiteness identifies that sum with the finite-fragment map despite its zero fallback.

**Theorem 1.4 (Real Laplace transform of total fragment mass).**

Lean statement: `D5/S3/PrimeGaps/FragmentLaplaceTransform.integral_exp_neg_mass_fragmentLaw`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentLaplaceTransform.integral_exp_neg_mass_fragmentLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive zeta and nonnegative s, the expectation of exp(-s times the total fragment mass) equals exp of the interval integral from zero to zeta of (exp(-s u)-1)/u. Specializing the Laplace functional to the constant test ofReal(s) gives the identity. The bound between zero and s for (1-exp(-s u))/u on the positive cutoff interval supplies integrability for conversion to real integrals.

## References

- Truth anchor: `D5/S3/PrimeGaps/FragmentLaplaceTransform.exp_neg_ennreal_sum`
- Truth anchor: `D5/S3/PrimeGaps/FragmentLaplaceTransform.integral_exp_neg_mass_fragmentLaw`
- Truth anchor: `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_finitePoissonLaw`
- Truth anchor: `D5/S3/PrimeGaps/FragmentLaplaceTransform.lintegral_exp_neg_fragmentLaw`
- Dependency: [D5/S3/PrimeGaps/FragmentLaw](FragmentLaw.md)
