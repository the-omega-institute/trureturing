# Skewed Independent Kill Rate

## Abstract

A finite behavior distribution replaces the uniform fixed fraction by weighted fixed-point mass.

**Theorem 1.1 (Weighted fixed mass skews the independent kill rate).**

$$\forall Y, Outcome, \operatorname{Fintype}(Y), \operatorname{MeasurableSpace}(Outcome), q: \operatorname{PMF}(Y), f: Y \to Y, mu: \operatorname{Measure}(Outcome), C, V: \operatorname{Set}(Outcome), coverageRate: ENNReal, (\operatorname{IndepSet}(C, V, mu) \land mu(C) = coverageRate \land mu(V) = escapeMass(q, f)) \Rightarrow (escapeMass(q, f) = 1-fixedMass(q, f) \land mu(\operatorname{inter}(C, V)) = coverageRate \times (1-fixedMass(q, f))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/SkewedIndependentKillRate.skewed_independent_kill_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixedMass term sums q over outputs fixed by f, so it is q(Fix f), a distributional mass rather than an alphabet cardinality. Its complement is the visible mutation mass escapeMass.

Let C be the coverage event and V the visibility event. The hypotheses say that C and V are independent, that C has the named coverage rate, and that V has the escape mass induced by q and f. The intersection is therefore the coverage rate multiplied by one minus the weighted fixed-point mass.

The proof composes the frozen weighted complement law with the frozen independent event product law. Uniform behavior is not assumed. Multi-site mutations and regression-based estimation are outside this statement.

## References

- Truth anchor: `D5/S0/Naming/SkewedIndependentKillRate.skewed_independent_kill_rate`
- Dependency: [D5/S0/Asymptotics/SkewedEscapeMass](../Asymptotics/SkewedEscapeMass.md)
- Dependency: [D5/S0/Naming/IndependentKillRate](IndependentKillRate.md)
