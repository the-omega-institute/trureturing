# Positive Periods for Discrete Observations

## Abstract

Every continuous discrete observation of an onto compact equicontinuous system has a positive period, obtained from the finite permutation of its complete names.

**Theorem 1.1 (From equicontinuity to a finite permutation).**

$$\begin{aligned}\forall D: Type,\\\forall A: Type,\\{}[\operatorname{UniformSpace}(D)]\\{}[\operatorname{CompactSpace}(D)]\\{}[\operatorname{TopologicalSpace}(A)]\\{}[\operatorname{DiscreteTopology}(A)]\\\forall T: D \Rightarrow D,\\\forall q: D \Rightarrow A,\\\operatorname{Function.Surjective}(T) \Rightarrow\\\operatorname{Continuous}(q) \Rightarrow\\\operatorname{Equicontinuous}(n: \mathbb{N} \mapsto \operatorname{Function.iterate}(T, n)) \Rightarrow\\\exists M: \mathbb{N}, 0 < M \land \forall x: D, q(\operatorname{Function.iterate}(T, M)(x)) = q(x)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObservationPeriod.finite_observation_period_of_equicontinuous_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Let D be an arbitrary compact uniform space, A a topological space with discrete topology, T:D→D onto, and q:D→A continuous. Assume the family of all forward iterates of T is equicontinuous. There is a natural number M>0 such that q(T^M(x))=q(x) for every x in D. The quantifier for q precedes that for M: the period depends on the observer. Neither A nor D is required to be finite or nonempty. There is no Hausdorff, zero-dimensional, metric or countability assumption on D, and no injectivity or invertibility assumption on T. Continuity of T follows from equicontinuity of the family at the iterate 1.

Define the complete name W(x)(n)=q(T^n(x)). The relation E={(x,y):q(x)=q(y)} is open and contains the diagonal. On a compact uniform space every such diagonal neighborhood is an entourage. Equicontinuity at x therefore supplies one neighborhood on which W(y)(n)=W(x)(n) simultaneously for all n. This proves local constancy of the whole-name map, a stronger assertion than continuity into the product topology. Compactness and IsLocallyConstant.range_finite make its actual image S finite; finiteness of S is a conclusion, not an input.

Left shift preserves S because W(T(x))(n)=W(x)(n+1). Onto T gives a predecessor for every realized name, so shift:S→S is onto and hence a finite permutation. Mathlib's Function.injective_iff_iterate_factorial_card_eq_id gives shift^(|S|!)=id. Its exponent is positive, including the empty-image case 0!=1. The map x↦W(x), valued in S, semiconjugates T to shift. Transporting the factorial iterate along this semiconjugacy and evaluating coordinate zero gives q(T^M(x))=q(x). No global point period is asserted.

For the stable-core application, let X be a compact Hausdorff uniform space with continuous f and let C=⋂n range(f^n). Supply its actual compact restriction TC:C→C, its surjectivity, and Subtype.val∘TC=f∘Subtype.val. Equicontinuity of the ambient iterates on C transfers through the uniform embedding Subtype.val to equicontinuity of TC's iterates. Restricting each continuous finite observer q to C gives an observer-dependent positive period there. StableCoreObservation.finite_observation_range_finite_of_stable_core_periodic then gives finitely many complete q-names on all of X, including transient points. This inference assumes the stated core restriction and does not construct it or establish its equicontinuity.

If X is also zero-dimensional, the finite-name conclusion for every finite continuous observation feeds FiniteObservationShadowing.initial_point_tracing_of_finite_observation_names. For each finite open cover U, that theorem constructs a finite open control cover V, and every V-pseudo-orbit a is U-traced by a(0) at all natural times including zero. This is an application of the existing complete-name and control-cover results, combined with the new period construction. It supplies no relative Boolean extension, and Peng's general Question 5.1 remains open. The construction is repository-derived and makes no literature priority claim.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObservationPeriod.finite_observation_period_of_equicontinuous_surjective`
- Dependency: [D5/S1/Dynamics/Shadowing/CompactObservationSubshift](CompactObservationSubshift.md)
