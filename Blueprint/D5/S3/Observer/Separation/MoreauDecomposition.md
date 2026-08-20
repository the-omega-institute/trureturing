# Moreau Decomposition

## Abstract

Every vector has a unique orthogonal decomposition across a closed convex cone and its polar.

**Theorem 1.1 (Closed convex cones admit a unique Moreau decomposition).**

$$\begin{gathered}\forall E: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(E)],\\{}[\operatorname{InnerProductSpace}(\mathbb{R}, E)],\\{}[\operatorname{CompleteSpace}(E)],\\C: \operatorname{ProperCone}(\mathbb{R}, E), x: E,\\\exists! p, r: E,\\p \in C \land -r \in \operatorname{InnerDual}(C) \land \\\langle p, r \rangle = 0 \land x = p + r.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/MoreauDecomposition.moreau_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a closed convex cone in a complete real inner-product space. Every vector x decomposes uniquely as x = p + r, where p belongs to C, r belongs to the polar cone, and p is orthogonal to r.

Mathlib defines the inner dual using nonnegative pairings. Accordingly, polar membership of r is represented by membership of minus r in the inner dual of C; this is exactly the nonpositive-pairing convention for the polar cone.

Existence uses the Hilbert projection theorem and its variational characterization. Testing the variational inequality at zero, twice the projection, and a translated cone point proves orthogonality and polar membership.

For uniqueness, compare two admissible decompositions. The two polar inequalities make the self-inner-product of the difference of their cone components nonpositive; positivity forces that difference to vanish, and the residual components then agree.

Repository search found the existing cone residual witness but no full existence-and-uniqueness declaration. Pinned Mathlib and Loogle supplied the projection existence and variational lemmas; a Loogle name query for Moreau returned zero declarations.

## References

- Truth anchor: `D5/S3/Observer/Separation/MoreauDecomposition.moreau_decomposition`
