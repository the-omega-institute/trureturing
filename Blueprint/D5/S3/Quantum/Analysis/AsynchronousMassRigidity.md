# Asynchronous rigidity of all multilinear masses

## Abstract

Positive asynchronous invariance forces every real multilinear mass to factor.

At a global maximum on K to the power I, strict positivity of the scalar weights forces every updated scalar term to equal that maximum. For each slot, its maximizing section is a nonempty compact convex invariant subset of K. It contains the same mass-one fixed vector sigma by CompactConvexFixedState. Replacing finitely many slots by sigma preserves the maximum. Apply the argument to minus F to obtain the same minimum. The normalized cube is therefore constant. A coordinatewise span induction extends this equality to every real tuple. This applies to periodic maps and boundary sigma. It asserts neither convergence of Phi iterates nor convergence of asynchronous iterates, rates, physical copies, or a tensor cone.

**Theorem 1.1 (Factorization on all real inputs).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall vI \in \operatorname{Universe}\left(\right),\; \forall I \in \operatorname{Type}\left(vI\right),\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \forall K \in \operatorname{Set}\left(A\right),\; \forall alpha \in I \to \operatorname{Real}\left(\right),\; \forall F \in \operatorname{MultilinearMap}\left(\operatorname{Real}\left(\right), \operatorname{constantFamily}\left(I, A\right), \operatorname{Real}\left(\right)\right),\; \operatorname{comp}\left(u, Phi\right) = u \Rightarrow \left(\left(\forall f \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(f, Phi\right) = f \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; f = \operatorname{smul}\left(c, u\right)\right)\right) \Rightarrow \left(\operatorname{IsCompact}\left(K\right) \Rightarrow \left(\operatorname{Nonempty}\left(K\right) \Rightarrow \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), K\right) \Rightarrow \left(\operatorname{span}\left(\operatorname{Real}\left(\right), K\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right) \Rightarrow \left(\operatorname{MapsTo}\left(Phi, K, K\right) \Rightarrow \left(\left(\forall x \in A,\; \operatorname{Mem}\left(x, K\right) \Rightarrow u\left(x\right) = 1\right) \Rightarrow \left(\left(\forall i \in I,\; 0 < alpha\left(i\right)\right) \Rightarrow \left(\operatorname{sum}\left(alpha\right) = 1 \Rightarrow \left(\left(\forall a \in I \to A,\; \operatorname{Mem}\left(a, \operatorname{pi}\left(\operatorname{univ}\left(I\right), {i:I}\mapsto K\right)\right) \Rightarrow F\left(a\right) = \operatorname{sum}\left({i:I}\mapsto alpha\left(i\right) \cdot F\left(\operatorname{update}\left(a, i, Phi\left(a\left(i\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; \forall a \in I \to A,\; F\left(a\right) = c \cdot \operatorname{prod}\left({i:I}\mapsto u\left(a\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.multilinear_mass_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I is any finite index type. Alpha is strictly positive at every index and sums to one. K is a compact convex spanning normalized set, and Phi preserves K and u. The original-cone applications supply the entire normalized base. The full real fixed dual is the line of u. F is an arbitrary real multilinear form; its continuity is proved by a finite basis expansion. Its asynchronous identity need only hold on every normalized tuple. The conclusion holds on all real inputs, with no additional factorization or fixed-tensor hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/AsynchronousMassRigidity.multilinear_mass_factorization`
- Dependency: [D5/S3/Quantum/Analysis/CompactConvexFixedState](CompactConvexFixedState.md)
