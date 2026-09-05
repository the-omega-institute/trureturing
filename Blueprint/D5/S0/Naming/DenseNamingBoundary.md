# Dense Naming Boundary

## Abstract

Separating discrete names force dense stated boundaries when every open region contains a nontrivial connected piece.

**Theorem 1.1 (Separating discrete names have dense boundary union).**

$$\forall X, \nu, B,\\\operatorname{HasNontrivialPreconnectedOpenPieces}\left(X\right) \land \operatorname{ContinuousAway}\left(\nu, B\right) \land \operatorname{SeparatesPoints}\left(\nu\right) \Rightarrow \operatorname{Dense}\left(\operatorname{iUnion}\left(B\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/DenseNamingBoundary.dense_iUnion_namingBoundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every nonempty open region contains an open preconnected subset with two distinct points. Each discrete-valued name is continuous off its stated boundary, and the complete family separates points.

If some nonempty open region avoided every boundary, choose two distinct points in its preconnected piece. IsPreconnected.constant makes every name equal on that pair, contradicting separation.

The local connected-piece premise corrects the unrestricted source claim. It is indispensable, as the following discrete counterexample shows.

**Theorem 1.2 (The unrestricted dense-boundary claim fails on a discrete space).**

$$\exists \nu, B,\\\operatorname{ContinuousAway}\left(\nu, B\right) \land \operatorname{SeparatesPoints}\left(\nu\right) \land \neg\operatorname{Dense}\left(\operatorname{iUnion}\left(B\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/DenseNamingBoundary.unrestricted_dense_boundary_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On discrete Bool, repeat the identity name at every natural index and state every boundary to be empty. The names are continuous and separate the two points, but their boundary union is empty and hence not dense.

## References

- Truth anchor: `D5/S0/Naming/DenseNamingBoundary.dense_iUnion_namingBoundary`
- Truth anchor: `D5/S0/Naming/DenseNamingBoundary.unrestricted_dense_boundary_fails`
