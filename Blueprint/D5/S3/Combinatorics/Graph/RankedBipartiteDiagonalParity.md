# Diagonal parity in ranked bipartite graphs

## Abstract

Compute the parity of the diagonal of each rank below an exceptional row.

**Theorem 1.1 (Diagonal parity from an oriented rank cut).**

$$\forall V \in Type,\; \forall rho \in V \to \mathrm{Nat},\; \forall e \in V \to \left(V \to \mathrm{Nat}\right),\; \forall t \in V,\; \forall r \in \mathrm{Nat},\; ((\operatorname{Finite}\left(V\right)) \land ((r < \operatorname{rho}\left(t\right)) \land ((\forall a \in V,\; \forall b \in V,\; ((a \ne t) \land (\operatorname{e}\left(a, b\right) \ne 0)) \Rightarrow ((a = b) \lor (\operatorname{rho}\left(a\right) < \operatorname{rho}\left(b\right)))) \land (\forall a \in V,\; (\operatorname{rho}\left(a\right) \le r) \Rightarrow ((\operatorname{mod}\left(\operatorname{Row}\left(a\right), 2\right) = 1) \land (\operatorname{mod}\left(\operatorname{Col}\left(a\right), 2\right) = 1)))))) \Rightarrow (\operatorname{mod}\left(\operatorname{Diag}\left(r\right), 2\right) = \operatorname{mod}\left(\operatorname{LayerSize}\left(r\right) + \operatorname{Inflow}\left(r\right) + \operatorname{Bypass}\left(r\right), 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/RankedBipartiteDiagonalParity.diagonal_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two copies of a finite vertex set with natural-number ranks. Every ordered pair has a nonnegative integer edge multiplicity. Outside a designated left vertex, each positive entry is diagonal or goes to a strictly higher rank. Fix a rank r below the designated vertex. Every row and every column through rank r has odd total multiplicity.

Row and Col are the sums of all multiplicities in the given row and column, respectively. Diag is the sum of diagonal entries at rank r. LayerSize counts vertices at rank r. Inflow sums multiplicities from the designated row to columns of rank at most r. Bypass sums multiplicities from rows of rank strictly below r to columns of rank strictly above r.

The row and column sums through rank r have equal parity. Their internal entries cancel, so the outgoing sum has the parity of the incoming sum. Split the outgoing sum into entries from rank r and entries bypassing r. The rank-r rows contribute only their diagonal and outgoing entries. Their total has the parity of the layer size.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/RankedBipartiteDiagonalParity.diagonal_parity`
