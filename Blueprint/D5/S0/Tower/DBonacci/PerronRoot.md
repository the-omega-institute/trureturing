# D-Bonacci Perron Root

## Abstract

The d-bonacci Perron root is unique, strictly increases with the order, and tends to two.

For order d at least two, divide the characteristic equation by x^d. The resulting finite reciprocal sum is continuous and strictly decreasing on the positive reals, while its values at one and two straddle one. This gives the unique root in the open interval without numerical approximation.

**Theorem 1.1 (Exact d-bonacci root characterization).**

$$\forall d \in N,\; d \ge 2 \Rightarrow \left(\forall x \in R,\; x = \operatorname{beta}\left(d\right) \Leftrightarrow \left(1 < x \land \left(x < 2 \land \operatorname{pow}\left(x, d\right) = \operatorname{sumPowersBelow}\left(x, d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.eq_dbonacciPerronRoot_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the reciprocal sum by x^d and reflecting the finite index range recovers x^d=sum(i=0,...,d-1)x^i. Strict decrease proves that every real in (1,2) satisfying this equation equals the chosen root.

**Theorem 1.2 (Characteristic and nontrivial equations agree).**

$$\forall d \in N,\; \forall x \in R,\; x \ne 1 \Rightarrow \left(\operatorname{pow}\left(x, d\right) = \operatorname{sumPowersBelow}\left(x, d\right) \Leftrightarrow \operatorname{pow}\left(x, d + 1\right) = 2 \cdot \operatorname{pow}\left(x, d\right) - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.dbonacci_characteristic_iff_nontrivial_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite geometric-sum identity introduces the factor x-1. Cancelling that factor away from the trivial root gives x^(d+1)=2x^d-1 in both directions.

**Theorem 1.3 (Perron roots strictly increase with order).**

$$\operatorname{StrictMonoOn}\left(\mathit{beta}, \operatorname{Ici}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Passing from d to d+1 adds one strictly positive reciprocal-power term. The next strictly decreasing reciprocal sum can therefore return to one only at a strictly larger argument.

**Theorem 1.4 (Order-two root is the golden ratio).**

$$\operatorname{beta}\left(2\right) = \mathit{goldenRatio}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_two_eq_goldenRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's goldenRatio lies in (1,2) and satisfies phi^2=phi+1. The exact root characterization therefore identifies beta(2) with it, without introducing another golden-ratio definition.

**Theorem 1.5 (Order-three root is the frozen Tribonacci constant).**

$$\operatorname{beta}\left(3\right) = \mathit{tribonacciConstant}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-three characteristic sum is beta^2+beta+1. The frozen Tribonacci root characterization then identifies beta(3) with the existing tribonacciConstant rather than redefining that constant.

**Theorem 1.6 (Perron roots tend to two).**

$$\operatorname{limitAtTop}\left(d, \operatorname{beta}\left(d\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_tendsto_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nontrivial equation gives the exact deficit 2-beta(d)=beta(d)^(-d). Monotonicity bounds beta(d) below by the golden ratio for every d at least two, so the deficit is squeezed by a geometric sequence tending to zero.

This is a filter-level Tendsto theorem as d goes to infinity, not a finite table or a numerical proximity check.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_strictMonoOn`
- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_tendsto_two`
- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant`
- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_two_eq_goldenRatio`
- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.dbonacci_characteristic_iff_nontrivial_equation`
- Truth anchor: `D5/S0/Tower/DBonacci/PerronRoot.eq_dbonacciPerronRoot_iff`
- Dependency: [D5/S0/Tower/Tribonacci/PerronRoot](../Tribonacci/PerronRoot.md)
