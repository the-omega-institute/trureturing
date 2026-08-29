# Global Prime-Exponent Realizability

## Abstract

Independent geometric prime exponents come from one positive-integer law exactly above the zeta threshold, and that law is unique.

**Definition 1.1 (Geometric prime mass).**

Lean statement: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.geometricPrimeMass`

*Formalization.* `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.geometricPrimeMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the prescribed zero-start geometric mass at a prime.

**Definition 1.2 (Prime-exponent code).**

Lean statement: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.primeExponentCode`

*Formalization.* `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.primeExponentCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This function records every prime exponent in a natural number.

**Definition 1.3 (Realization of the prime-exponent law).**

Lean statement: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.RealizesPrimeExponentLaw`

*Formalization.* `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.RealizesPrimeExponentLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A realization has no mass at zero, independent exponent coordinates, and every prescribed geometric marginal.

**Theorem 1.4 (Positive support is necessary for exponent-code uniqueness).**

$$\operatorname{map}\left(V, \Delta_0\right)=\operatorname{map}\left(V, \Delta_1\right) \land \Delta_0\neq\Delta_1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.positive_integer_support_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Point masses at zero and one are distinct but have the same complete prime-exponent code, so excluding zero is necessary.

**Theorem 1.5 (The zero-exponent mass).**

$$g_{s,p}(0)=1-p^{-s}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.geometric_prime_mass_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent zero the geometric factor is one, leaving one minus the prime activation probability.

**Theorem 1.6 (The zeta law realizes the exponent family).**

$$1<s \Rightarrow \operatorname{Realizes}\left(s, \zeta_{s}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.zeta_realizes_prime_exponent_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one, the repository zeta distribution has independent prime factorizations and the required geometric marginals.

**Theorem 1.7 (Global realizability has threshold one).**

$$(\exists q, \operatorname{Realizes}\left(s, q\right)) \Leftrightarrow 1<s.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.global_prime_exponent_realizable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existence above one is supplied by the zeta distribution.

At positive exponents at most one, the canonical product gives finite-support profiles measure zero by the prime-series threshold and Borel-Cantelli. Nonpositive exponents already make a prescribed prime marginal have total mass zero.

**Theorem 1.8 (The realization is unique).**

$$1<s \land \operatorname{Realizes}\left(s, q\right) \Rightarrow q=\zeta_{s}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.prime_exponent_realization_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independence identifies the joint exponent product law. Unique prime factorization recovers each positive natural-number atom.

**Theorem 1.9 (The unique mass is the normalized zeta weight).**

$$q(n)=\frac{n^{-s}}{\zeta(s)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.prime_exponent_realization_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every atom equals its power-law weight divided by the real zeta partition function.

**Theorem 1.10 (Exponent zero is not realizable).**

$$\neg \exists q, \operatorname{Realizes}\left(0, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.zero_exponent_not_realizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold theorem rules out the concrete exponent zero.

**Theorem 1.11 (The critical exponent is not realizable).**

$$\neg \exists q, \operatorname{Realizes}\left(1, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.critical_exponent_not_realizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold theorem also rules out the critical exponent one.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.RealizesPrimeExponentLaw`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.critical_exponent_not_realizable`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.geometricPrimeMass`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.geometric_prime_mass_zero`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.global_prime_exponent_realizable_iff`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.positive_integer_support_is_necessary`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.primeExponentCode`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.prime_exponent_realization_mass`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.prime_exponent_realization_unique`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.zero_exponent_not_realizable`
- Truth anchor: `D5/S3/Analytic/PrimeProducts/GlobalPrimeExponentRealizability.zeta_realizes_prime_exponent_law`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast](FiniteMarginalGlobalSupportContrast.md)
