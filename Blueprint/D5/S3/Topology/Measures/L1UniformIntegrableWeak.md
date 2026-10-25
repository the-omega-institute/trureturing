# Weak sequential compactness from uniform integrability

## Abstract

Uniform integrability gives a genuinely weakly convergent real L1 subsequence over any finite measure.

RealLone(mu) denotes MeasureTheory.Lp Real 1 mu, and representatives(f) denotes its actual coerced representative sequence. The sigma algebra is arbitrary and the finite measure may be zero. No nonatomicity, countable generation, positivity or ambient separability is assumed.

**Theorem 1.1 (A weak subsequence for every uniformly integrable real L1 sequence).**

$$\begin{aligned}\forall Omega: Type_{u}, [\operatorname{MeasurableSpace}\left(Omega\right)] \forall mu: \operatorname{Measure}\left(Omega\right), [\operatorname{IsFiniteMeasure}\left(mu\right)] \\\forall f: \operatorname{Nat}\left(\right) \to \operatorname{RealLone}\left(mu\right), \operatorname{UniformIntegrable}\left(\operatorname{representatives}\left(f\right), 1, mu\right) \Rightarrow\\\exists j:\operatorname{Nat}\left(\right) \to \operatorname{Nat}\left(\right), \exists v:\operatorname{RealLone}\left(mu\right), \operatorname{StrictMono}\left(j\right) \land \forall phi: \operatorname{ContinuousRealLinearFunctional}\left(\operatorname{RealLone}\left(mu\right)\right), \operatorname{Tendsto}\left(n \mapsto \operatorname{apply}\left(phi, \operatorname{apply}\left(f, \operatorname{apply}\left(j, n\right)\right)\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{apply}\left(phi, v\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1UniformIntegrableWeak.exists_weak_subsequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib UniformIntegrable.spec supplies uniform hard-tail bounds at errors 1/(m+1). Restriction to the strict complementary level set gives bounded L2 functions. The inclusion L2 → L1 preserves the identical almost-everywhere class and is bounded by the finite-measure exponent comparison, including zero total measure. The common Hilbert approximation theorem therefore gives one increasing selector and an actual L1 limit, tested against every continuous real linear functional. This proves the weak-extraction part of the classical subsequence-splitting argument. It supplies neither the disjoint-carrier selection nor the signed-measure transfer or the full CH/Talagrand conclusion.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1UniformIntegrableWeak.exists_weak_subsequence`
- Dependency: [D5/S3/Topology/Measures/L1WeakExtraction](L1WeakExtraction.md)
