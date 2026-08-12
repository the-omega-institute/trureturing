# Unimodular Monomial Substitution

## Abstract

The determinant-one monomial substitution has an explicit inverse on nonzero pairs.

**Theorem 1.1 (The substitution is inverted by two monomials).**

$$P = u^{2} / v, Q = v^{2} / u^{3}, u \neq 0, v \neq 0 \Rightarrow P^{2}Q = u \land P^{3}Q^{2} = v.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/UnimodularMonomialSubstitution.unimodular_monomial_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source atom explicitly displays the change of variables P = u^2/v and Q = v^2/u^3 and calls its exponent matrix determinant one. This partial closure isolates exactly the resulting inverse formula on the nonzero coordinate domain.

Substitution reduces the first recovered coordinate to u^4 v^2 divided by v^2 u^3, and the second to u^6 v^4 divided by v^3 u^6. The nonzero hypotheses discharge both denominators.

Pinned Mathlib was searched before proving. No exact theorem for this monomial substitution was found; the proof uses its field normalizer for the component identities.

## References

- Truth anchor: `D5/S3/Factorization/UnimodularMonomialSubstitution.unimodular_monomial_substitution`
