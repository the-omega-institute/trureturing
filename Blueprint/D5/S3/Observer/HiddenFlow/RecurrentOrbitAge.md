# Recurrent Orbits Have No Continuous Age

## Abstract

A recurrent real flow orbit admits no continuous clock equal to elapsed time.

**Theorem 1.1 (A recurrent orbit has no continuous age).**

$$\forall X, [\operatorname{TopologicalSpace}(X)],\ \phi: \operatorname{Flow}(\mathbb{R}, X), x_0: X, times: \mathbb{N} \to \mathbb{R},\ (\operatorname{Tendsto}(times, \operatorname{atTop}, \operatorname{atTop}) \land \operatorname{Tendsto}((n \mapsto \phi_{times_{n}}(x_0)), \operatorname{atTop}, \operatorname{nhds}(x_0))) \Rightarrow\ \neg\exists age: X \to \mathbb{R},\ \operatorname{Continuous}(age) \land \forall t\in \mathbb{R}, 0 \leq t \Rightarrow age(\phi_{t}(x_0)) = t.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/RecurrentOrbitAge.recurrent_orbit_has_no_continuous_age` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Phi be a continuous real flow on a topological space X. Assume a sequence of times tends to positive infinity while the corresponding orbit points converge back to x0.

Continuity would make the proposed age values along those orbit points converge to age(x0). The clock identity applies at all sufficiently large sequence times, so the same values tend to positive infinity. The two limits are incompatible.

Loogle supplied Continuous.tendsto, Tendsto.eventually, and Tendsto.congr'. LeanSearch supplied the exact contradiction theorem not_tendsto_atTop_of_tendsto_nhds; each supporting result is imported and applied. No full-statement library or repository match was found. The identity flow on Unit with natural-number real times is a checked recurrence witness.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/RecurrentOrbitAge.recurrent_orbit_has_no_continuous_age`
