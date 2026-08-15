# Finite-Distance Invariant Sectors

## Abstract

Finite observer distance forces equal evaluation on every bounded invariant observable.

**Theorem 1.1 (Finite-distance points share an invariant sector).**

$$\forall I: \operatorname{Type}, \tau: \operatorname{Perm}(I), x, y: I,\ d_\tau(x, y) \neq \infty \Rightarrow \forall f: I \to \operatorname{Complex},\ \operatorname{Bounded}(f) \Rightarrow L_\tau(f) = 0 \Rightarrow f(x) = f(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FiniteDistanceInvariantSector.finite_distance_same_invariant_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau be a permutation and let x and y have finite extended observer distance. Then every bounded complex observable with zero update defect takes the same value at x and y.

If such an observable separated the points, the frozen invariant-separation theorem would force their observer distance to be infinity, contrary to finiteness. Equality on every invariant observable is precisely the fiber condition for the restriction-by-evaluation map.

Repository and pinned-Mathlib searches found no existing finite-distance fiber theorem. The proof imports and directly applies the repository's general invariant-separation theorem by contrapositive. Loogle found no exact upstream match.

## References

- Truth anchor: `D5/S3/Observer/Separation/FiniteDistanceInvariantSector.finite_distance_same_invariant_sector`
- Dependency: [D5/S3/Observer/Separation/InvariantObservableInfinity](InvariantObservableInfinity.md)
