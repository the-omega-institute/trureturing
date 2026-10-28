# Exact Native Unary Block Exchanges

## Abstract

Every minimum unary-source mask has exact descent under every admissible exchange.

The first source is inserted and the second source is the base. Both are nonempty. A native admissible cut exchanges two whole adjacent maximal runs with the required exterior U-run. Either source may be unary; the two orientations are proved with their distinct degree formulas.

**Theorem 1.1 (Lower bound for every exchange).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall u \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \forall E \in \operatorname{BlockCut}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \forall a \in alpha,\; \forall n \in \operatorname{Nat}\left(\right),\; \left(u \ne nil \land \left(\operatorname{ValidMask}\left(u, v, \operatorname{original}\left(E\right), M\right) \land \left(\operatorname{Admissible}\left(E, M\right) \land \left(u = \operatorname{replicate}\left(n, a\right) \lor v = \operatorname{replicate}\left(n, a\right)\right)\right)\right)\right) \Rightarrow \left(\exists s \in \operatorname{Nat}\left(\right),\; \exists t \in \operatorname{Nat}\left(\right),\; \operatorname{degree}\left(u, v, \operatorname{original}\left(E\right)\right) = s \land \left(\operatorname{degree}\left(u, v, \operatorname{successor}\left(E\right)\right) = t \land s \le t + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryExchange.exchange_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete the actual block whose label belongs to the unary source. Its letters are all a, and the deleted word has both reduced ordered source projections. The old and exchanged words reinsert the same mass at two actual cuts. The indexed gap transport identifies the changed gap at each cut, including cuts separated by any number of zero-mass gaps. Adding mass increases the occupied-gap count by at most one; in the reverse orientation only internal gaps contribute. This gives the lower bound without assuming commutation of the non-unary projection.

**Theorem 1.2 (Every minimum mask and every exchange).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall u \in \operatorname{List}\left(alpha\right),\; \forall v \in \operatorname{List}\left(alpha\right),\; \forall E \in \operatorname{BlockCut}\left(alpha\right),\; \forall M \in \operatorname{List}\left(Side\right),\; \forall r \in \operatorname{Nat}\left(\right),\; \left(u \ne nil \land \left(v \ne nil \land \left(\operatorname{IsMinimumMask}\left(u, v, \operatorname{original}\left(E\right), M, r\right) \land \left(2 \le r \land \left(\operatorname{Admissible}\left(E, M\right) \land \left(\left(\exists a \in alpha,\; \exists m \in \operatorname{Nat}\left(\right),\; 1 \le m \land u = \operatorname{replicate}\left(m, a\right)\right) \lor \left(\exists a \in alpha,\; \exists n \in \operatorname{Nat}\left(\right),\; 1 \le n \land v = \operatorname{replicate}\left(n, a\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{degree}\left(u, v, \operatorname{successor}\left(E\right)\right) = \operatorname{NatSub}\left(r, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesUnaryExchange.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>1, every minimum mask M and every admissible cut E, the successor degree is exactly r-1. The common-deletion lower bound gives at least r-1. The original native intended-successor theorem gives a valid successor mask with exactly r-1 U-runs and hence the matching upper bound. Both exchange directions are included. No choice of a preferred minimum mask is made, and no statement about an empty inserted source is inferred.

## References

- Truth anchor: `D5/S1/Words/HughesUnaryExchange.exchange_lower`
- Truth anchor: `D5/S1/Words/HughesUnaryExchange.result`
- Dependency: [D5/S1/Words/HughesUnaryInsertion](HughesUnaryInsertion.md)
