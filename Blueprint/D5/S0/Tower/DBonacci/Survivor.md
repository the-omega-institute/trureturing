# D-Bonacci Survivor Carrier

## Abstract

D-bonacci name grids carry a common normalized distance, compatible with order three.

**Definition 1.1 (Intrinsic d-bonacci name grid).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{dbonacciNameGrid}\left(d, Q\right) = \operatorname{range}\left(\operatorname{dbonacciNameValue}\left(d, Q\right)\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/Survivor.dbonacciNameGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The level-Q grid is the image of every admissible d-bonacci name under the existing intrinsic value map.

**Definition 1.2 (Normalized d-bonacci survivor carrier).**

$$\forall d \in N,\; \forall Q \in N,\; \forall x \in R,\; \operatorname{dbonacciSurvivor}\left(d, Q, x\right) = \operatorname{beta}\left(d\right)^{Q} \cdot \operatorname{infDist}\left(x, \operatorname{dbonacciNameGrid}\left(d, Q\right)\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each level, metric infimum distance to the actual finite name grid is normalized by the Q-th power of the already frozen Perron root.

**Theorem 1.3 (Order-three specialization is the frozen Tribonacci carrier).**

$$\forall Q \in N,\; \forall x \in R,\; \operatorname{dbonacciSurvivor}\left(3, Q, x\right) = \operatorname{tribonacciSurvivor}\left(Q, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor_three_eq_tribonacciSurvivor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general order-three admissibility predicate has the same names as the frozen Tribonacci automaton, their value images agree, and the existing Perron-root bridge identifies the normalization constants.

**Theorem 1.4 (Every survivor value of order at least two is nonnegative).**

$$\forall d \in N,\; \forall Q \in N,\; \forall x \in R,\; d \ge 2 \Rightarrow \operatorname{dbonacciSurvivor}\left(d, Q, x\right) \ge 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the Perron normalization and nonnegativity of metric infimum distance give the sign directly.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Survivor.dbonacciNameGrid`
- Truth anchor: `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor`
- Truth anchor: `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor_nonneg`
- Truth anchor: `D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor_three_eq_tribonacciSurvivor`
- Dependency: [D5/S0/Tower/DBonacci/Values](Values.md)
- Dependency: [D5/S0/Tower/Tribonacci/Survivor](../Tribonacci/Survivor.md)
