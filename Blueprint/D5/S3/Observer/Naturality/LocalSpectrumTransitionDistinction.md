# Local Spectrum Transition Distinction

## Abstract

Equal local spectra can hide distinct axes related by an observer transition.

**Theorem 1.1 (Equal local spectra can hide an axis transition).**

$$\forall G \in Type, A \in Type, X \in Type, Y \in Type, S \in Type,\; \left(\operatorname{Group}\left(G\right) \land \left(\operatorname{MulAction}\left(G, A\right) \land \left(\operatorname{MulAction}\left(G, X\right) \land \left(\operatorname{IsPretransitive}\left(G, A\right) \land \operatorname{Nontrivial}\left(A\right)\right)\right)\right)\right) \Rightarrow \left(\forall O \in A \to \left(X \to Y\right), U \in G \to \operatorname{Equiv}\left(Y, Y\right), q \in A \to S,\; \left(\left(\forall g \in G, a \in A, x \in X,\; O\left(\operatorname{smul}\left(g, a\right), \operatorname{smul}\left(g, x\right)\right) = U\left(g\right)\left(O\left(a, x\right)\right)\right) \land \left(\forall g \in G, a \in A,\; q\left(\operatorname{smul}\left(g, a\right)\right) = q\left(a\right)\right)\right) \Rightarrow \left(\left(\neg \left(\exists d \in S \to A,\; \operatorname{LeftInverse}\left(d, q\right)\right)\right) \land \left(\exists a \in A, b \in A, g \in G, T \in \operatorname{Equiv}\left(\operatorname{range}\left(O\left(a\right)\right), \operatorname{range}\left(O\left(b\right)\right)\right),\; a \ne b \land \left(q\left(a\right) = q\left(b\right) \land \left(\operatorname{smul}\left(g, a\right) = b \land \left(\forall x \in X,\; T\left(O\left(a, x\right)\right) = U\left(g\right)\left(O\left(a, x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/LocalSpectrumTransitionDistinction.local_spectrum_transition_distinction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local-spectrum readout is invariant under a transitive action on a nontrivial axis space, so it has no left-inverse absolute-axis decoder.

The declaration exposes distinct axes with equal local spectra together with the group element, observer-world equivalence, and transition computation rule relating those same axes.

## References

- Truth anchor: `D5/S3/Observer/Naturality/LocalSpectrumTransitionDistinction.local_spectrum_transition_distinction`
- Dependency: [D5/S3/Observer/Naturality/InvariantOriginRecoveryObstruction](InvariantOriginRecoveryObstruction.md)
- Dependency: [D5/S3/Observer/Naturality/ObserverWorldCovariance](ObserverWorldCovariance.md)
