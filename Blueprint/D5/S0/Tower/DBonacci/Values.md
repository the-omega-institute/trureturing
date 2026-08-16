# D-Bonacci Values

## Abstract

D-bonacci names acquire real values from the order-d Perron root.

A true digit in position i contributes beta_d to the negative power i+1. The prefix enumeration follows the same finite run-budget split that counts admissible names, so its order is canonical rather than chosen.

**Definition 1.1 (D-bonacci name value).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{dbonacciNameValue}\left(d, Q\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/Values.dbonacciNameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is the finite base-beta_d sum over the true positions of an admissible Boolean word.

**Definition 1.2 (Indexed d-bonacci name value).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{indexedNameValue}\left(d, Q\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/Values.indexedNameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursive equivalence lists false-prefix names before true-prefix names at every run-budget state.

**Theorem 1.3 (Order-three values agree with Tribonacci).**

$$\forall Q \in N,\; \operatorname{dbonacciNameValue}\left(3, Q, \mathit{word}\right) = \operatorname{tribonacciNameValue}\left(Q, \mathit{word}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Values.dbonacciNameValue_three_eq_tribonacciNameValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The already proved identity beta_3=t makes the two word sums equal term by term; the bridge therefore preserves the underlying word.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Values.dbonacciNameValue`
- Truth anchor: `D5/S0/Tower/DBonacci/Values.dbonacciNameValue_three_eq_tribonacciNameValue`
- Truth anchor: `D5/S0/Tower/DBonacci/Values.indexedNameValue`
- Dependency: [D5/S0/Tower/DBonacci/Names](Names.md)
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](PerronRoot.md)
