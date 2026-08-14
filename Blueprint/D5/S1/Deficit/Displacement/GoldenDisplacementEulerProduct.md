# Golden Displacement Euler Product

## Abstract

The hidden golden-substitution product is multiplicative on coprimes and yields an absolutely convergent two-variable Euler product.

**Theorem 1.1 (The hidden product has an exact prime-power formula).**

$$\forall p, e\in\mathbb{N},\ p \text{prime} \implies nS(p^{e}) = p^{\operatorname{start}(e)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prime power has factorization support at one prime with exponent e. Evaluating the finite product defining nS therefore replaces that lone exponent by its golden substitution start, while the zero-exponent case reduces to the unit.

**Theorem 1.2 (The hidden product is multiplicative on coprime factors).**

$$\forall m, n\in\mathbb{N},\ \gcd(m,n) = 1 \implies nS(mn) = nS(m) \cdot nS(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprime natural numbers have disjoint prime-factorization supports. The factorization of their product is the sum of the two exponent maps, so the finite product for nS splits across those disjoint supports into the product of the two nS values.

**Theorem 1.3 (The hidden product is not completely multiplicative).**

$$\exists p\in\mathbb{N},\ p \text{prime} \land nS(p^{2}) \neq nS(p)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_not_completelyMultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the prime two, one substitution exponent is two but the substitution exponent at level two is three rather than four. The prime-power formula consequently gives nS of four as eight, whereas the square of nS of two is sixteen.

**Theorem 1.4 (Every nonzero input divides its hidden product).**

$$\forall n\in\mathbb{N},\ n\neq0 \implies \exists k\in\mathbb{N},\ nS(n) = nk$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dvd_nS` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden substitution start of every exponent is at least that exponent. Comparing the prime-factorization exponents of n and nS n therefore proves divisibility coordinate by coordinate; nonzeroness supplies the factorization criterion.

**Theorem 1.5 (The displacement term is multiplicative on coprime factors).**

$$\forall s, w\in\mathbb{R},\ \forall m, n\in\mathbb{N},\ \gcd(m,n) = 1 \implies D_{s,w}(mn) = D_{s,w}(m) \cdot D_{s,w}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero coprime inputs, coprime multiplicativity of nS and the real-power law split both factors in the displacement term. If either input is zero, coprimality forces the other to be one, and the explicitly defined zero and unit values close the case.

**Theorem 1.6 (The displacement series converges absolutely).**

$$\forall s, w\in\mathbb{R},\ 0 \leq s \land 1 < s+w \implies \sum_{n\in\mathbb{N}}\lvert D_{s,w}(n)\rvert < \infty$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divisibility gives n at most nS n. When s is nonnegative, raising both quantities to the nonpositive exponent minus s bounds each displacement term by n to the power minus s minus w. The convergent natural-power series supplies domination.

**Theorem 1.7 (Prime powers give the Hecke-Mahler local monomials).**

$$\forall s, w\in\mathbb{R},\ \forall p, e\in\mathbb{N},\ p \text{prime} \implies D_{s,w}(p^{e}) = (p^{-s})^{\operatorname{start}(e)} \cdot (p^{-w})^{e}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the exact nS prime-power formula into the displacement definition separates the real powers of p. The real-power multiplication identities then rewrite the result as the local two-variable monomial indexed by the exponent e.

**Theorem 1.8 (The displacement surface has an Euler product).**

$$\forall s, w\in\mathbb{R},\ 0 \leq s \land 1 < s+w \implies \prod_{p \text{prime}}(\sum_{e\in\mathbb{N}}(p^{-s})^{\operatorname{start}(e)} \cdot (p^{-w})^{e}) = \sum_{n\in\mathbb{N}}D_{s,w}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.displacement_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned mathlib Euler-product theorem applies to the displacement term using its unit value, zero value, coprime multiplicativity, and absolute summability. A termwise rewrite by the prime-power formula identifies every local factor with the displayed two-variable Hecke-Mahler series.

**Theorem 1.9 (The zero-displacement cross-section is the zeta series).**

$$\forall w\in\mathbb{R},\ \sum_{n\in\mathbb{N}}D_{0,w}(n) = \sum_{n\in\mathbb{N}, n\neq0}n^{-w}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.zeta_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Setting s to zero makes the hidden-product factor equal one at every nonzero n, while the displacement definition keeps the zero term equal to zero. Termwise congruence therefore identifies the resulting series with the ordinary zeta Dirichlet series over positive natural numbers.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_mul_of_coprime`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_prime_pow`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dTerm_summable`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.displacement_euler_product`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.dvd_nS`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_mul_of_coprime`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_not_completelyMultiplicative`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.nS_prime_pow`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.zeta_section`
- Dependency: [D5/S1/Deficit/Displacement/GoldenSubstitutionOrbit](GoldenSubstitutionOrbit.md)
