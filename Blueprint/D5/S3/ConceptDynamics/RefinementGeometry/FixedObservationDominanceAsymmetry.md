# Fixed Observation Dominance Asymmetry

## Abstract

Complete dominance is asymmetric under one fixed indexed observation language.

**Theorem 1.1 (Fixed-observation complete dominance is asymmetric).**

$$\begin{aligned}\forall A, C, X, I: \operatorname{Type},\\O: I \to \operatorname{Type},\\realization: \operatorname{Sym2}\left(A\right) \to C \to X,\\q: \forall i: I, X \to O_{i},\\a, b: A, c: C,\\\operatorname{let} profile : = \operatorname{jointReadout}\left(q\right),\\\operatorname{dominates}\left(l: A, r: A\right): \operatorname{Prop} : = (\operatorname{profile}\left(\operatorname{realization}\left(\operatorname{s}\left(l, l\right), c\right)\right) = \operatorname{profile}\left(\operatorname{realization}\left(\operatorname{s}\left(l, r\right), c\right)\right) \land \operatorname{profile}\left(\operatorname{realization}\left(\operatorname{s}\left(l, r\right), c\right)\right) \neq \operatorname{profile}\left(\operatorname{realization}\left(\operatorname{s}\left(r, r\right), c\right)\right)) \operatorname{in}\\\operatorname{dominates}\left(a, b\right) \Rightarrow \neg\operatorname{dominates}\left(b, a\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/FixedObservationDominanceAsymmetry.fixed_observation_dominance_asymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diploid genotypes are unordered pairs of alleles. The deterministic realization map sends each genotype and context to an internal state, and the canonical joint readout constructs the fixed observation language's profile.

Dominance of the left allele means that the left homozygote and shared heterozygote have equal profiles while that heterozygote and the right homozygote have unequal profiles. Reversing dominance would require the latter two profiles to be equal, which is impossible.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/FixedObservationDominanceAsymmetry.fixed_observation_dominance_asymmetric`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
