# Positive-Measure Naming Jurisdictions

## Abstract

Positive-measure naming jurisdictions contain uncountably many source points.

**Theorem 1.1 (Positive-measure jurisdictions are uncountable).**

$$\begin{gathered}\forall X, system, encode, name,\\system: NamingSystem(X), encode: X\to Name(system), name: Name(system),\\NoAtoms(\mu) \land 0< \mu(fiber(encode, name)) \Rightarrow \neg Countable(fiber(encode, name)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/PositiveMeasureJurisdiction.positive_measure_jurisdiction_uncountable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let system be a naming system on a measured source X, let encode map source points to its names, and let name be one such name. The jurisdiction of name is the fiber of encode over name.

If the source measure is atomless and that jurisdiction has positive measure, then the jurisdiction is not countable.

The proof applies Mathlib's Set.Countable.measure_zero directly: a countable jurisdiction would have zero measure, contradicting the positive-measure hypothesis.

## References

- Truth anchor: `D5/S0/Naming/Conservation/PositiveMeasureJurisdiction.positive_measure_jurisdiction_uncountable`
- Dependency: [D5/S0/Naming/NamingSystem](../NamingSystem.md)
