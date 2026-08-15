# Eventual Cycle Average

## Abstract

An eventually cyclic orbit has long-run observable average equal to its cycle average.

**Theorem 1.1 (Eventually cyclic orbits have the cycle average).**

$$\forall Y, F: Y \to Y, v: Y \to \mathbb{R}, a\in Y,\ \forall \lambda\in \mathbb{N}, 0 < \lambda, p: \operatorname{Fin}(\lambda) \to Y, \mu\in \mathbb{N},\ (\forall n\in \mathbb{N}, F^{\mu+n}(a) = p_{n \operatorname{mod} \lambda}) \Rightarrow\ \lim_{T\to\infty} \frac{\sum_{t=0}^{T-1} v(F^{t}(a))}{T} = \frac{\sum_{j=0}^{\lambda-1} v(p_{j})}{\lambda}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let update be a self-map of Y, let value be a real-valued observable, and start the orbit at initial. Assume there is a positive period lambda, an entry time mu, and a cycle p such that every iterate after mu is p indexed modulo lambda.

Then the finite-horizon observable average converges to the uniform average of value over the cycle. The proof splits the orbit into its fixed prefix, complete cycle blocks, and one bounded remainder block.

Loogle found the exact pinned-library limits tendsto_mod_div_atTop_nhds_zero_nat and tendsto_natCast_div_add_atTop; both are imported and applied. LeanSearch returned the convergent-sequence averaging theorem, fixed-point orbit averages, and bounded shift differences, but no nonconstant periodic-orbit average theorem. Repository and formalization searches found no duplicate. A one-state Boolean orbit witnesses satisfiable hypotheses.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average`
