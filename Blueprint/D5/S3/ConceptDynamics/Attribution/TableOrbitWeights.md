# The orbit program for finite equivariant probability kernels

## Abstract

Orbit mass variables for invariant probability tables and their event constraints.

**Theorem 1.1 (Invariant event masses are exactly the linear combinations of orbit frequencies).**

$$\forall G, T, A, m, (\exists p, \operatorname{InvariantLaw}\left(G, T, A, m, p\right)) \iff (\exists z, \operatorname{FeasibleOrbitMasses}\left(G, T, A, m, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.invariant_event_masses_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a finite type T. Events A are finite subsets of T indexed by an arbitrary type I, and m gives their prescribed real masses. An invariant law on T has nonnegative weights summing to one and is constant on every orbit. The orbit frequency of an event counts its intersection with the orbit and divides by the orbit size.

An invariant law with the prescribed event masses gives orbit totals that are nonnegative and sum to one. Conversely, distribute each orbit total uniformly within its orbit. Every prescribed event is then recovered by the same linear combination of its orbit frequencies.

**Theorem 1.2 (The orbit program attains the maximum invariant mass of the target event).**

$$\operatorname{InvariantEventConstraintsFeasible}\left(A, m\right) \Rightarrow \exists z, \operatorname{OptimalOrbitMasses}\left(A, m, B, z\right) \land \operatorname{SameAttainableTargetMasses}\left(A, m, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_invariant_event_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an additional target event B in a finite G-set. Assume that some invariant probability law has all the prescribed event masses. The feasible orbit totals form a nonempty closed subset of a compact box. The target mass is a linear objective and has a maximizer there.

For every real value a, an invariant law satisfying the event constraints and assigning a to B exists exactly when a feasible orbit vector has objective value a.

**Theorem 1.3 (An arbitrary subgroup's fixed seed mass is the attained orbit program optimum).**

$$\operatorname{Subgroup}\left(H, G\right) \land \operatorname{NonemptyFiniteInput}\left(X, v\right) \land \operatorname{FiniteOutputWithDecidableEquality}\left(Y, w\right) \land \operatorname{FiniteTableType}\left(X, Y\right) \land \operatorname{CovariantProbabilityKernel}\left(G, X, Y, P\right) \Rightarrow \exists z, \operatorname{OptimalKernelOrbitMasses}\left(H, P, z\right) \land \operatorname{UniversalCalibrationBound}\left(H, P, z, s\right) \land \operatorname{PositiveCalibrationAttainment}\left(H, P, z, \operatorname{MaxUniverse}\left(v, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_table_fixed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group G acts on a nonempty finite input type X in universe v and a finite output type Y in universe w with decidable equality. The deterministic table type has a finite enumeration. Let H be a subgroup of G and let P be a G-covariant probability kernel. The table action simultaneously transports arguments and outputs. The linear constraints prescribe all evaluation marginals, and the target event consists of the tables fixed by H.

The chosen vector of orbit totals is feasible and maximizes the target objective over every feasible vector. That value bounds the H-fixed mass of every finite seed type in arbitrary universe s with nonnegative, normalized, G-invariant weights and a G-covariant deterministic readout having marginals P. A finite seed type in the maximum of v and w attains the value with strictly positive normalized G-invariant weights and a G-covariant deterministic readout with marginals P.

Pushing a calibration to its deterministic tables preserves the marginals and can increase the fixed mass. The optimizer lifts back by restricting its table law to the positive support and taking evaluation as the deterministic readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.invariant_event_masses_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_invariant_event_mass`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_table_fixed_mass`
- Dependency: [D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass](NormalSubgroupFixedMass.md)
