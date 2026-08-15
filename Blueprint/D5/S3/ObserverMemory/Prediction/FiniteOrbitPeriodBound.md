# Finite Orbit Period Bound

## Abstract

Finite deterministic orbits and their readouts have a cardinality-bounded tail period.

**Theorem 1.1 (Finite orbits have cardinality-bounded tail periods).**

$$\forall Y, O,\ [\operatorname{Fintype} Y],\ F: Y \to Y, q: Y \to O,\ \forall y_{0}\in Y,\ \exists mu, p\in \mathbb{N},\ 0 < p \land mu+p \leq \operatorname{card}(Y) \land \forall t\in \mathbb{N},\ mu \leq t \Rightarrow (F^{t+p}(y_{0}) = F^{t}(y_{0}) \land q(F^{t+p}(y_{0})) = q(F^{t}(y_{0}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state carrier, F a deterministic self-map, q any readout, and y0 an initial state. Some strictly positive period p begins after a tail index mu, with mu+p no larger than the number of states.

For every time t at or after mu, shifting by p preserves the state. Applying q to that state equality gives the same period for every deterministic readout.

Pinned Mathlib and Loogle gave the exact pigeonhole declaration Fintype.exists_ne_map_eq_of_card_lt. The proof applies it to the first card(Y)+1 orbit points and uses Function.iterate_add_apply to propagate the collision. Pinned-Mathlib and repository searches found no equal or stronger quantitative theorem. LeanSearch's API endpoint returned HTTP 404 and supplied no search conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic`
