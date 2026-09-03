# Golden Euler Beta Zeckendorf Ledger

## Abstract

The golden Euler exponent ledger has a closed Beatty form whose floor and jumps are read from the canonical Zeckendorf expansion.

**Theorem 1.1 (Least-index parity controls the golden Euler beta ledger).**

$$\left(\forall v \in N,\; \operatorname{o5Beta}\left(v\right) = \left\lfloor\frac{v + 1}{\varphi}\right\rfloor + v \cdot \varphi\right) \land \left(\left(\forall n \in N,\; 0 < n \Rightarrow \left\lfloor\frac{n}{\varphi}\right\rfloor = \sum_{k \in \operatorname{zeck}\left(n\right)} \operatorname{fib}\left(k - 1\right) - \operatorname{ite}\left(\operatorname{Even}\left(\operatorname{lastIdx}\left(n\right)\right), 1, 0\right)\right) \land \left(\forall v \in N,\; \operatorname{o5Beta}\left(v + 1\right) - \operatorname{o5Beta}\left(v\right) = \operatorname{ite}\left(\operatorname{Even}\left(\operatorname{lastIdx}\left(v + 1\right)\right), \varphi^{2}, \varphi\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenEulerBetaZeckendorf.golden_euler_beta_zeckendorf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural v, the frozen exponent o5Beta is the Beatty floor of (v+1)/phi plus v phi. For positive n, that floor is the sum of Fibonacci numbers obtained by lowering every index in the canonical Zeckendorf expansion, with a correction of one exactly when the least index is even.

Here zeck(n) is the canonical descending Zeckendorf index list and lastIdx(n) is its final, hence least, index. The same parity test selects the next ledger jump: phi squared for an even least index of v+1, and phi for an odd least index.

This result is an exponent-accounting characterization. It does not assert an all-order germ extraction, O-5, analytic continuation, or the Riemann Hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/GoldenEulerBetaZeckendorf.golden_euler_beta_zeckendorf`
