# Double-Insertion Prefix-Reversal Coordinates

## Abstract

Two independently specified insertion gaps classify every configuration with the same double-deletion residual up to reversal.

Configurations at dimension m+2 assign labels to positions bijectively. Choose an actual tuple z whose penultimate and last labels are t and s. Its double-deletion residual P is obtained by deleting s and then t from its oriented circular tuple. DoubleStar(t,s,P) consists of all configurations having residual P or its reverse. This domain is specified independently of a path or its scanned support. The labels t and s differ because z is a permutation.

**Theorem 1.1 (The Independent Two-Gap Bijection).**

$$\forall m \in \mathrm{Nat},\; (3 \le m) \Rightarrow (\forall z \in \mathrm{Configuration}\left(m + 1\right),\; \mathrm{Bijective}\left(\mathrm{doubleInsertionMap}\left(z\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates.doubleInsertion_coordinates_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three the configurations in DoubleStar(t,s,P) are in bijection with Fin(m) times Fin(m+1) times Fin(m+2) times Bool. The first coordinate chooses the gap of t among the residual labels; the second chooses the gap of s among the resulting m+1 labels. The remaining coordinates specify the rotation and reflection of the actual tuple. Consequently this independently defined domain has 2m(m+1)(m+2) elements.

Let a, b and c reverse the first m+2, m+1 and m positions. The coordinate operation d reverses the first m-1 positions. The product cd rotates the first m residual labels and fixes t,s. Thus the outer anchors are z(cd)^k and their current circles after deleting s are (rotate_k(R),t), where R is the first m labels of z. Within each current circle the native single-deletion coordinates give z(cd)^k(bc)^l(ab)^r, followed by a when the Bool coordinate is true. The operation d describes coordinates only.

To find a coordinate for an arbitrary configuration, first rotate its full tuple to put s last, then rotate its first m+1 positions to put t penultimate. Its remaining m-label tuple has circular residual P or its reverse. Reverse this block in the latter case, then compare rotations with R. This gives an outer anchor and the fixed-current-circle coordinates give the other three coordinates. For uniqueness, the successor of t in the current circle determines its outer gap. Two outer current circles cannot be reverses: deleting t would make the nodup residual P equal to its reverse, which is impossible on at least three labels. The inner native-coordinate bijection then determines the rest.

**Definition 1.2 (The Coordinate Equivalence).**

$$\forall m \in \mathrm{Nat},\; (3 \le m) \Rightarrow (\forall z \in \mathrm{Configuration}\left(m + 1\right),\; \mathrm{Equiv}\left(\mathrm{Product}\left(\mathrm{Fin}\left(m\right), \mathrm{Product}\left(\mathrm{Fin}\left(m + 1\right), \mathrm{Product}\left(\mathrm{Fin}\left(m + 2\right), \mathrm{Bool}\right)\right)\right), \mathrm{Subtype}\left(\mathrm{DoubleStar}\left(\mathrm{apply}\left(z, \mathrm{penultimatePosition}\left(m\right)\right), \mathrm{apply}\left(z, \mathrm{lastPosition}\left(m + 1\right)\right), \mathrm{delete}\left(\mathrm{apply}\left(z, \mathrm{penultimatePosition}\left(m\right)\right), \mathrm{delete}\left(\mathrm{apply}\left(z, \mathrm{lastPosition}\left(m + 1\right)\right), \mathrm{configurationCycle}\left(z\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates.doubleInsertionCoordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bijective actual coordinate map defines an equivalence between the four coordinate factors and the independent double-deletion subtype. Its forward map is doubleInsertionMap, and its inverse recovers the unique insertion gaps, cyclic position and reflection direction. This equivalence transports the independently measured finite domain to native coordinates.

The coordinate bijection classifies a double-deletion domain. Constructing a generator cycle on this domain additionally requires actual component paths and converting edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates.doubleInsertionCoordinateEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates.doubleInsertion_coordinates_bijective`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](PrefixReversalZeroStarComplement.md)
