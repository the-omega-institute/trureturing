# Commuting Reversible Realization

## Abstract

Commuting finite realizations have exact itinerary capacity and a tail-shift reversibility criterion.

**Theorem 1.1 (Exact capacity, reversible existence, and stabilization).**

$$(\forall M, I, F, g, C\left(M, I, F, g\right) \Rightarrow (\forall x \in S, \forall j \in \mathbb{N}, g\left(F^{j}\left(I\left(x\right)\right)\right) = q\left(D^{j}\left(x\right)\right)) \land K \le \operatorname{card}\left(\operatorname{range}\left(I\right)\right) \le \operatorname{card}\left(M\right) \land (\operatorname{Bijective}\left(F\right) \Rightarrow \operatorname{Bijective}\left(sigma\right))) \land\\{}\operatorname{Finite}\left(T\right) \land \operatorname{Surjective}\left(iota\right) \land C\left(T, iota, sigma, gT\right) \land\\{}((\exists M, I, F, g, C\left(M, I, F, g\right) \land \operatorname{Bijective}\left(F\right)) \iff \operatorname{Injective}\left(sigma\right)) \land\\{}(\operatorname{Injective}\left(sigma\right) \iff \operatorname{Bijective}\left(sigma\right)) \land\\{}(K = N_{n} \iff R_{n} = R_{n + 1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/CommutingReversibleRealization.commuting_reversible_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a nonempty finite source, A a finite alphabet, D a total source update, q its readout, and n a nonnegative horizon. The complete itinerary iota(s) has coordinate j equal to q(D^j(s)). Let T be its actual range, K its cardinality, sigma the tail shift on T, and gT(t) the coordinate t(0). Let W_n be the range of words through time n, N_n its cardinality, and R_n the kernel of the finite-word map.

Write C(M,I,F,g) for a finite total carrier M with total preparation I, update F and readout g, satisfying I(D(s)) = F(I(s)) and g(F^j(I(s))) = q(D^j(s)) for every source s and every 0 <= j <= n. The quantifiers over implementations below use exactly this condition. No surjectivity of I is required for the lower bound.

The first clause gives correctness at every future time and counts both the prepared image and the whole carrier. The second gives the explicit K-state implementation M = T with surjective preparation. Together they make K the exact minimum. If sigma is injective, finiteness makes this same implementation reversible, so the reversible minimum is also K.

For necessity, commutation makes P = I(S) forward invariant. An injective update restricts to a bijection on finite P. The surjective behavioral factor from P to T intertwines the updates; lifting a state of T first to P and then to a predecessor proves that sigma is surjective. Finiteness then gives injectivity. Unprepared states and duplicated behaviors do not alter this argument.

For the final equivalence, prefix projection is a surjection from T to W_n. Equal cardinalities make it injective, identifying R_n with the complete itinerary kernel. This kernel lies inside R_(n+1), which lies inside R_n. Conversely, equality of consecutive kernels identifies the stable finite quotient with the complete quotient, giving equal cardinalities.

## References

- Truth anchor: `D5/S3/ObserverMemory/Realization/CommutingReversibleRealization.commuting_reversible_realization`
- Dependency: [D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization](CanonicalMinimalRealization.md)
- Dependency: [D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity](FreeWindowRealizationCapacity.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/GradedPredictionShift](../Refinement/GradedPredictionShift.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/FutureItineraryShift](../Trajectories/FutureItineraryShift.md)
