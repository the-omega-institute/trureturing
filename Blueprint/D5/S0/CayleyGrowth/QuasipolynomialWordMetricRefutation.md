# Quasipolynomial Word Metric Refutation

## Abstract

A closed-form transposition family whose word metric is not eventually quasipolynomial.

**Theorem 1.1 (The square indicator admits no eventual quasipolynomial).**

Lean statement: `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.not_eventuallyQuasipolynomial_of_eventually_squareIndicator`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.not_eventuallyQuasipolynomial_of_eventually_squareIndicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational function of a natural argument is eventually quasipolynomial when some period admits one rational polynomial per residue class, agreeing with the function beyond some threshold; no degree bound is imposed. Suppose a function takes the value one at every perfect square and zero at every nonsquare, from some point on. Then it is not eventually quasipolynomial. Fix a period and look only at the residue class of zero. The squares of the multiples of the period lie in that class and are squares; adding the period to each of them gives numbers of the same class lying strictly between consecutive squares, hence nonsquares, because the period is at most twice the multiple. Shifting the index past both thresholds keeps both families infinite. The constituent polynomial of that one class therefore takes the value one on an infinite set and the value zero on another, so it equals both the constant one and the constant zero. The other constituents are never constrained.

**Theorem 1.2 (Refutation of the marked-element growth conjecture).**

Lean statement: `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.cayleyPy_conjecture2_refuted`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.cayleyPy_conjecture2_refuted` (`✓ std3`). ∎

*Citation.* A. Chervov and others (2025). *CayleyPy Growth: Efficient growth computations and hundreds of new conjectures on Cayley graphs*. DOI: [10.48550/arXiv.2509.19162](https://doi.org/10.48550/arXiv.2509.19162).

*Commentary.*

The literature note attests the conjecture, not this theorem. Take as generators every transposition of the finite type of size n, and as marked element the transposition of the first two indices when n is at least two and a perfect square, the identity otherwise. In the Cayley graph of that generating set the marked element is adjacent to the identity at square sizes, since a transposition is a generator and differs from the identity, and equal to the identity elsewhere. The distance from the identity is therefore one at squares of size at least two and zero at nonsquares, which is the square indicator. By the preceding theorem that distance is not eventually quasipolynomial of any degree, so in particular it is not given by a quadratic or linear quasipolynomial. Both objects are written by closed formulas and a square test, so the polynomial-time hypothesis of the conjecture holds of them; that hypothesis is discharged outside the formal statement.

## References

- Truth anchor: `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.cayleyPy_conjecture2_refuted`
- Truth anchor: `D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation.not_eventuallyQuasipolynomial_of_eventually_squareIndicator`
