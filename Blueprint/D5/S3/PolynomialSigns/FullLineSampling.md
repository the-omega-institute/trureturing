# Joint signs on the real line

## Abstract

Every jointly realized sign vector of a finite real polynomial family occurs on one tail, at a common product root, or at a common critical point.

**Definition 1.1 (Three sign codes).**

Lean statement: `D5/S3/PolynomialSigns/FullLineSampling.ternary`

*Formalization.* `D5/S3/PolynomialSigns/FullLineSampling.ternary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real a, ternary(a) is 0 when a < 0, 1 when a = 0, and 2 when a > 0. Its codomain is Fin 3.

**Theorem 1.2 (One representative for the entire sign vector).**

$$\forall m \in Nat,\; \forall f \in Fin\left(m\right) \to Polynomial\left(Real\right),\; \forall s \in Fin\left(m\right) \to Fin\left(3\right),\; \left(\exists y \in Real,\; \forall i \in Fin\left(m\right),\; ternary\left(eval\left(f\left(i\right), y\right)\right) = s\left(i\right)\right) \Leftrightarrow \left(PositiveTail\left(f, s\right) \lor \left(NegativeTail\left(f, s\right) \lor \left(\left(\exists r \in Roots\left(P\left(f\right)\right),\; \forall i \in Fin\left(m\right),\; ternary\left(eval\left(f\left(i\right), r\right)\right) = s\left(i\right)\right) \lor \left(\exists r \in Roots\left(derivative\left(P\left(f\right)\right)\right),\; \forall i \in Fin\left(m\right),\; ternary\left(eval\left(f\left(i\right), r\right)\right) = s\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PolynomialSigns/FullLineSampling.full_line_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m, every family f indexed by Fin m of real univariate polynomials, and every s from Fin m to Fin 3, put P(f) equal to the product over all i of 1 if f(i) is the zero polynomial, and f(i) otherwise. Roots(q) means the finite support q.roots.toFinset. In the formula, signs(f,y) means that for every i in Fin m, ternary(f(i).eval(y)) = s(i). PositiveTail(f,s) means that for every i, ternary(f(i).leadingCoeff) = s(i). NegativeTail(f,s) instead uses the leading coefficient of f(i) composed with -X.

The same real y realizes every prescribed sign. Each root alternative also uses one common r for all members; individually attainable signs are insufficient. If y is not a product root, the nearest product roots bound a root-free interval, or y lies in an outer cell. Rolle's theorem supplies a critical point in each bounded interval. The intermediate value theorem keeps every nonzero member's sign fixed throughout that interval. On an outer cell the finite family has simultaneous eventual signs determined by the corresponding leading coefficients.

No nonzero, positive-degree, squarefree or coprime hypothesis is imposed on the family. Empty families, zero polynomials, constants and repeated roots are included. P(f) is always nonzero. When its derivative is zero, the derivative root support is empty; it does not represent every real zero of the zero polynomial. The result is a universal sampling characterization over arbitrary real coefficients. It gives no effective executable procedure or complexity bound.

## References

- Truth anchor: `D5/S3/PolynomialSigns/FullLineSampling.full_line_sampling`
- Truth anchor: `D5/S3/PolynomialSigns/FullLineSampling.ternary`
