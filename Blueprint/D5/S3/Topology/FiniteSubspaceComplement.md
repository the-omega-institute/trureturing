# Path connected complements of finite subspace families

## Abstract

Two line segments join points in an open convex set while avoiding finitely many subspaces of codimension at least two.

**Theorem 1.1 (Avoiding finitely many subspaces in an open convex set).**

$$\begin{gathered}\forall E,J:\operatorname{Type}, [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)]\\{}[\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] [\operatorname{Finite}\left(J\right)],\\\forall U:\operatorname{Set}\left(E\right), P:J \to \operatorname{Submodule}\left(\mathbb{R}, E\right),\\\operatorname{IsOpen}\left(U\right) \land \operatorname{Convex}\left(\mathbb{R}, U\right) \land \operatorname{Nonempty}\left(U\right) \land (\forall i:J, \forall x:E, \operatorname{sup}\left(\operatorname{P}\left(i\right), \operatorname{span}\left(x\right)\right) \neq \operatorname{top}\left(E\right)) \Rightarrow\\\operatorname{IsPathConnected}\left(\operatorname{diff}\left(U, \operatorname{union}\left(P\right)\right)\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteSubspaceComplement.pathConnected_complement_in_open_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a finite-dimensional real normed space and U a nonempty open convex subset. The family P of linear subspaces of E has a finite index type. Assume that for each member P and each vector x, adding the line spanned by x to P gives a proper subspace of E. This expresses the codimension condition using subspace sums.

For any two endpoints in U outside the forbidden subspaces, exclude the subspaces obtained by adjoining either endpoint to each forbidden subspace. Each enlarged subspace is proper and closed, so its complement is dense and open. Their finite intersection meets U. Join both endpoints to a point in this intersection. If either segment met a forbidden subspace away from its original endpoint, solving its affine combination for the intermediate point would place that point in an enlarged subspace.

## References

- Truth anchor: `D5/S3/Topology/FiniteSubspaceComplement.pathConnected_complement_in_open_convex`
