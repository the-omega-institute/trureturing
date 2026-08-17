# Periodic Threshold Kernel

## Abstract

Reachable periodic states exactly control eventual threshold bounds on finite orbits.

**Theorem 1.1 (Eventual thresholds are controlled by reachable periodic states).**

$$\forall Y, [\operatorname{Finite}(Y)],\ F: Y \to Y, A \subseteq Y, v: Y \to \mathbb{R}, \alpha\in \mathbb{R},\ (\exists N\in \mathbb{N},\ \forall a\in A, t\in \mathbb{N},\ N \leq t \Rightarrow v(F^{t}(a)) \leq \alpha) \iff \forall p\in P_{F}(A),\ v(p) \leq \alpha.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Thresholds/PeriodicThresholdKernel.eventual_threshold_iff_reachable_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state carrier, F a deterministic self-map, A a set of allowed initial states, and v a real-valued observable. Write P_F(A) for the states on positive-period F-orbits that are reached by some finite iterate of a state in A.

There is one time N after which every orbit from A has value at most alpha if and only if every state in P_F(A) has value at most alpha. The reverse implication uses N equal to the number of states: by then every trajectory is in its reachable periodic core.

Repository search found and the proof applies the weaker quantitative finite-orbit period bound. Pinned Mathlib supplied periodicPts, IsPeriodicPt.mul_const, and iterate_add_apply, but no theorem with the full threshold equivalence. Three local smart-search queries also returned no full match. Loogle and LeanSearch were absent from the available NyxID services; two GitHub code-search proxy requests failed with HTTP 400 and supplied no conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Thresholds/PeriodicThresholdKernel.eventual_threshold_iff_reachable_periodic`
