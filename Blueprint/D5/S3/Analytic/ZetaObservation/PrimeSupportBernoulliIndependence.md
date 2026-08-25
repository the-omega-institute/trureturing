# Prime Support Bernoulli Independence

## Abstract

Prime support bits have their power-law Bernoulli marginals inside one mutually independent family.

**Theorem 1.1 (Prime support bits are independent Bernoulli variables).**

$$\forall s \in \mathbb{R},\; 1 < s \Rightarrow \left((\forall p \in \operatorname{Primes}\left(\right),\; \operatorname{LawUnder}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{SupportBit}\left(p\right)\right) = \operatorname{Bernoulli}\left(p^{{-s}}\right)) \land \operatorname{MutuallyIndependentUnder}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{PrimeIndexedFamily}\left(\operatorname{SupportBit}\left(\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence.prime_support_bits_independent_bernoulli` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the zeta distribution with exponent above one, the support bit at a prime records whether that prime has positive exponent. Its law is Bernoulli with parameter p to the power minus s.

The family statement uses the full prime-indexed independence predicate. It is obtained by mapping the already independent exponent coordinates through the positive-support predicate, so it controls every finite joint cylinder rather than only separate marginals.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence.prime_support_bits_independent_bernoulli`
