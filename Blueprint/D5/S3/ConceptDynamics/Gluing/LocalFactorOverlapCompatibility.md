# Local Factor Overlap Compatibility

## Abstract

Local factors of one target through a surjective readout agree on every overlap of their exact local domains.

**Theorem 1.1 (Local factors automatically agree on overlaps).**

$$\forall I \in \operatorname{Type}\left(\right), X \in \operatorname{Type}\left(\right), B \in \operatorname{Type}\left(\right), Y \in \operatorname{Type}\left(\right), q \in X \to B, T \in X \to Y, U \in I \to \left(B \to \operatorname{Prop}\left(\right)\right), f \in \forall i: I, \operatorname{Subtype}\left(U\left(i\right)\right) \to Y,\; \left(\operatorname{Surjective}\left(q\right) \land \left(\forall i \in I, x \in X,\; \operatorname{mem}\left(q\left(x\right), U\left(i\right)\right) \Rightarrow T\left(x\right) = \operatorname{localApply}\left(f, i, q\left(x\right)\right)\right)\right) \Rightarrow \left(\forall i \in I, j \in I, b \in B,\; \left(\operatorname{mem}\left(b, U\left(i\right)\right) \land \operatorname{mem}\left(b, U\left(j\right)\right)\right) \Rightarrow \operatorname{localApply}\left(f, i, b\right) = \operatorname{localApply}\left(f, j, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility.local_factor_overlap_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each local factor is defined on the subtype of base points belonging to its own domain, matching the source carrier rather than extending the function arbitrarily to the whole base.

For an overlap point b, surjectivity supplies x with q(x)=b. Both local factorization equations then identify their respective values at b with the same target value T(x).

Openness, cover-totality, and continuity are not used by this algebraic compatibility step; they belong to subsequent topological gluing. Repository and pinned-library searches found no exact theorem on the dependent local-domain carrier.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility.local_factor_overlap_compatibility`
