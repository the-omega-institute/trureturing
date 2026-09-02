# One-Step Closure Fivefold Equivalence

## Abstract

One-step kernel closure is equivalent to complete behavioral closure, exact descent, and absence of carry.

**Theorem 1.1 (Five closure criteria are equivalent).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}q: X \to B, F: X \to X,\\{}\operatorname{ListTFAE}\left({[\operatorname{depthZeroKernel}\left(q\right) = \operatorname{depthOneKernel}\left(q, F\right), \operatorname{InterfaceCongruence}\left(q, F\right), Setoid.ker q = Setoid.ker (\operatorname{completeItinerary}\left(F, q\right)), \operatorname{EffectiveDescent}\left(q, F\right), \forall x, y: X, \neg \operatorname{IsCarryWitness}\left(q, F, q, x, y\right)]}\right) \land\\{}((\exists x, y: X, \operatorname{IsCarryWitness}\left(q, F, q, x, y\right)) \iff \operatorname{depthOneKernel}\left(q, F\right) < \operatorname{depthZeroKernel}\left(q\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/OneStepClosureFivefoldEquivalence.one_step_closure_fivefold_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any state type, readout, and deterministic update, equality of the depth-zero and depth-one kernels is equivalent to forward fiber invariance, equality with the complete-itinerary kernel, unique effective descent on the realized image, and absence of carry.

The final clause identifies the complementary event: a carry witness exists exactly when the depth-one kernel is a strict refinement of the depth-zero kernel. No finiteness or nonemptiness assumption is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/OneStepClosureFivefoldEquivalence.one_step_closure_fivefold_equivalence`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../../ObserverMemory/Prediction/ItineraryCompletion.md)
