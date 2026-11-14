# Hanna A181316: all integer parameters

## Abstract

Integer coefficients of Hanna's full all-parameter q-integer exponential.

**Definition 1.1 (The literal rational logarithm).**

$$\forall q: \mathbb{Z}, \operatorname{logarithm}\left(q\right) = \operatorname{PowerSeries.mk}\left((fun n: \mathbb{N} \mapsto if n = 0 then 0 else \frac{\left((q: \mathbb{Q}) - 1\right) \cdot (\frac{(q: \mathbb{Q})^{n} - 1}{(q: \mathbb{Q}) - 1})^{n - 1}}{(n: \mathbb{Q})})\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.logarithm` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181316 all-parameter q-integer exponential integrality*. URL: <https://oeis.org/A181316>.

*Commentary.*

OEIS A181316, sole COMMENTS conjecture, revision 2 (unpaginated): "Conjecture: exp( Sum_{n>=1} (q-1)*((q^n-1)/(q-1))^(n-1)*x^n/n ) is an integer series for all integer q>1." The positive coefficient is exactly the source rational quotient and exponent. Its constant coefficient is zero. The variable q is an integer and n is a natural index.

**Definition 1.2 (The formal exponential).**

$$\forall q: \mathbb{Z}, \operatorname{A}\left(q\right) = \operatorname{PowerSeries.subst}\left(\operatorname{logarithm}\left(q\right), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181316 all-parameter q-integer exponential integrality*. URL: <https://oeis.org/A181316>.

*Commentary.*

The exponential is formal over Q. Substitution takes logarithm q first and exp Q second. The zero logarithm constant makes this the ordinary formal exponential, without analytic convergence.

**Definition 1.3 (The complete source assertion).**

$$(\operatorname{claim}) \iff (\forall q: \mathbb{Z}, (1 < q) \implies (\forall N: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(N, \operatorname{A}\left(q\right)\right) = (z: \mathbb{Q})))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A181316 all-parameter q-integer exponential integrality*. URL: <https://oeis.org/A181316>.

*Commentary.*

Conjecture: exp( Sum_{n>=1} (q-1)*((q^n-1)/(q-1))^(n-1)*x^n/n ) is an integer series for all integer q>1. Every integer q>1 and every natural degree N, including zero, is quantified. Integrality is an integer witness for each rational coefficient; there is no nonnegativity assertion.

**Theorem 1.4 (Integrality for every allowed parameter).**

$$\forall q: \mathbb{Z}, (1 < q) \implies (\forall N: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(N, \operatorname{A}\left(q\right)\right) = (z: \mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna181316` (proved) by `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna181316","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA181316Integrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A181316 all-parameter q-integer exponential integrality*. URL: <https://oeis.org/A181316>.

*Commentary.*

For q>=2 write S(n)=1+q+...+q^(n-1) and b(n)=(q-1)*S(n)^(n-1). The finite geometric identity identifies the literal quotient with S(n). Fix a prime p, n>0, and a=v_p(n). If p divides q-1, factoring S(p^a*t) into a geometric blocks proves p^a divides S(n). The factor q-1 supplies the remaining p in b(n) and b(p*n); a=0 is handled directly. If p does not divide q-1, the original fermat_lift theorem gives q^(p*n) congruent to q^n modulo p^(a+1), uniformly including p dividing q. Cancelling the prime unit q-1 gives S(p*n) congruent to S(n). For a unit S(n), Euler's theorem identifies the exponents p*n-1 and n-1. For a nonunit, n cannot equal p^a: Frobenius in ZMod p would otherwise give q^n=q and S(n)=1. Thus n=p^a*t with t>=2 and n-1>=a+1, so both powers vanish at the required modulus. This covers p=2, q=2, n=1 and every valuation. The existing DoldExponentialIntegrality.integral_exp_of_dold now proves all coefficients integral. The explicit conversion q.toNat covers every allowed integer q. No Euler-product machinery is reproved and no sign condition on its exponents is used.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.A`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.logarithm`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA181316Integrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](../Witt/HannaDiagonalGhostPowerIntegrality.md)
