# Associative matching sewing

## Abstract

Associative matching sewing

Boundary n is Bool times Fin n. Composite pairs exposed endpoints through the glued middle boundary. The internal loop count counts connected components that avoid every exposed endpoint. No planarity assumption is used.

**Theorem 1.1 (composite_assoc).**

$$\forall (n: \operatorname{Nat}), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (e: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (f: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\operatorname{composite}\left(\operatorname{composite}\left(d, e\right), f\right) = \operatorname{composite}\left(d, \operatorname{composite}\left(e, f\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.composite_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both bracketings induce the same exterior equivalence relation.

**Theorem 1.2 (internalLoopCount_cocycle).**

$$\forall (n: \operatorname{Nat}), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (e: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (f: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), ((\operatorname{internalLoopCount}\left(d, e\right)) + (\operatorname{internalLoopCount}\left(\operatorname{composite}\left(d, e\right), f\right)) = (\operatorname{internalLoopCount}\left(e, f\right)) + (\operatorname{internalLoopCount}\left(d, \operatorname{composite}\left(e, f\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sums count the closed components of the triple gluing.

**Theorem 1.3 (internalLoopCount_pos_assoc).**

$$\forall (n: \operatorname{Nat}), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (e: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (f: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (((0 < \operatorname{internalLoopCount}\left(d, e\right)) \lor (0 < \operatorname{internalLoopCount}\left(\operatorname{composite}\left(d, e\right), f\right))) \Leftrightarrow ((0 < \operatorname{internalLoopCount}\left(e, f\right)) \lor (0 < \operatorname{internalLoopCount}\left(d, \operatorname{composite}\left(e, f\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_pos_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A closed component occurs in one bracketing exactly when one occurs in the other.

## References

- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.composite_assoc`
- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_cocycle`
- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_pos_assoc`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](../Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](FiniteMatchingSewing.md)
