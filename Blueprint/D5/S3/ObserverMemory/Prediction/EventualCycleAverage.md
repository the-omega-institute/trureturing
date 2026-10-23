# Eventual Cycle Average

## Abstract

An eventually cyclic orbit has long-run observable average equal to its cycle average.

**Theorem 1.1 (Exact complete blocks and remainder).**

$$\forall p\in \mathbb{N}, 0 < p,\ \forall v: \operatorname{Fin}(p) \to \mathbb{R}, n\in \mathbb{N},\ \sum_{i=0}^{n-1} v(i \operatorname{mod} p) = \lfloor\frac{n}{p}\rfloor \cdot \sum_{i=0}^{p-1} v(i \operatorname{mod} p) + \sum_{i=0}^{n \operatorname{mod} p-1} v(i \operatorname{mod} p)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural period p, real-valued cycle v on Fin p, and natural horizon n, the sum of v at indices modulo p is exactly the natural quotient n divided by p times one full cycle sum, plus the sum over the remainder n modulo p. No sign or orbit assumption is required. Casting natural weights to real values lets this same identity supply exact update counts for periodic fixed-response paths.

**Theorem 1.2 (Eventually cyclic orbits have the cycle average).**

$$\forall Y, F: Y \to Y, v: Y \to \mathbb{R}, a\in Y,\ \forall \lambda\in \mathbb{N}, 0 < \lambda, p: \operatorname{Fin}(\lambda) \to Y, \mu\in \mathbb{N},\ (\forall n\in \mathbb{N}, F^{\mu+n}(a) = p_{n \operatorname{mod} \lambda}) \Rightarrow\ \lim_{T\to\infty} \frac{\sum_{t=0}^{T-1} v(F^{t}(a))}{T} = \frac{\sum_{j=0}^{\lambda-1} v(p_{j})}{\lambda}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let update be a self-map of Y, let value be a real-valued observable, and start the orbit at initial. Assume there is a positive period lambda, an entry time mu, and a cycle p such that every iterate after mu is p indexed modulo lambda.

Then the finite-horizon observable average converges to the uniform average of value over the cycle. The proof splits the orbit into its fixed prefix, complete cycle blocks, and one bounded remainder block.

The limit theorem tendsto_mod_div_atTop_nhds_zero_nat makes the remainder length divided by the horizon tend to zero. The remainder sum is bounded in absolute value by the sum of the absolute cycle values, so tendsto_bdd_div_atTop_nhds_zero makes its normalized contribution vanish. The same bounded-division theorem makes the fixed prefix contribution vanish, while tendsto_natCast_div_add_atTop makes the ratio n / (n + mu) tend to one. Thus adding the finite prefix preserves the cycle average. A one-state Boolean orbit witnesses satisfiable hypotheses.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder`
