# Complete Dominance and Observation Nonfaithfulness

## Abstract

Complete dominance between distinct realized genotypes requires a nonfaithful observation language and disappears under a separating readout.

**Theorem 1.1 (Complete dominance requires observation nonfaithfulness).**

$$\begin{aligned}\forall A, C, X, I: \operatorname{Type},\\O: I \to \operatorname{Type},\\realization: \operatorname{Sym2}\left(A\right) \to C \to X,\\q: (\forall i: I, X \to O_{i}),\\a, b: A, c: C,\\(\operatorname{realization}\left(\operatorname{s}\left(a, a\right), c\right) \ne \operatorname{realization}\left(\operatorname{s}\left(a, b\right), c\right) \land \operatorname{jointReadout}\left(q, \operatorname{realization}\left(\operatorname{s}\left(a, a\right), c\right)\right) = \operatorname{jointReadout}\left(q, \operatorname{realization}\left(\operatorname{s}\left(a, b\right), c\right)\right) \land \operatorname{jointReadout}\left(q, \operatorname{realization}\left(\operatorname{s}\left(a, b\right), c\right)\right) \ne \operatorname{jointReadout}\left(q, \operatorname{realization}\left(\operatorname{s}\left(b, b\right), c\right)\right)) \Rightarrow\\(\neg \operatorname{InjOn}\left(\operatorname{jointReadout}\left(q\right), \{\operatorname{realization}\left(\operatorname{s}\left(a, a\right), c\right), \operatorname{realization}\left(\operatorname{s}\left(a, b\right), c\right), \operatorname{realization}\left(\operatorname{s}\left(b, b\right), c\right)\}\right) \land (\forall i: I, \neg \operatorname{Injective}\left((g: \operatorname{Sym2}\left(A\right) \mapsto \operatorname{q}\left(i, \operatorname{realization}\left(g, c\right)\right))\right)) \land \exists d: X \to \operatorname{Prop}, \operatorname{d}\left(\operatorname{realization}\left(\operatorname{s}\left(a, a\right), c\right)\right) \ne \operatorname{d}\left(\operatorname{realization}\left(\operatorname{s}\left(a, b\right), c\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Faithfulness/CompleteDominanceObservationNonfaithfulness.complete_dominance_observation_nonfaithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A deterministic realization maps unordered diploid genotypes and a context to internal states. The canonical joint readout collects all coordinates of the chosen observation language.

Complete dominance identifies the profiles of the left homozygote and heterozygote while separating the heterozygote from the right homozygote. If the first two internal states are distinct, their shared profile makes the language noninjective on the three relevant states.

Consequently no coordinate already present can be injective on all genotypes under this realization and context. The equality predicate of the first state supplies another readout that distinguishes the latent pair, making the dependence on observation language explicit.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Faithfulness/CompleteDominanceObservationNonfaithfulness.complete_dominance_observation_nonfaithfulness`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](JointFaithfulnessLeibnizCriterion.md)
