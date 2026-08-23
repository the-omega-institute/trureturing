# Quotient Blindness to Diagonal Twists

## Abstract

A value interface invariant under a twist cannot detect that twist on diagonals.

**Theorem 1.1 (An invariant interface hides every diagonal twist).**

$$\forall A, Y, Z: \operatorname{Type},\ \forall q: Y \to Z, tau: Y \to Y, E: A \to \left(A \to Y\right),\ (q \circ tau = q) \Rightarrow q \circ \operatorname{diagonal}\left(tau, E\right) = q \circ \operatorname{diagonal}\left(id, E\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/QuotientTwistBlindness.quotient_twist_blindness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be an address type, Y a value type, Z an observed-value type, q map Y to Z, tau be a self-map of Y, and E be a table indexed twice by A. The twisted diagonal sends a to tau(E(a,a)); the untwisted diagonal sends a to E(a,a).

Assume q after tau equals q. Applying q coordinatewise to either diagonal then gives the same observed vector for every table E. Thus exact compatibility at the observed interface need not make the underlying twist visible; no injectivity or surjectivity of q is assumed.

Loogle and LeanSearch both returned Function.semiconj_iff_comp_eq for the composition hypothesis. The proof imports and applies the repository's stronger coordinate restriction naturality theorem at the identity address embedding and identity observed twist. Full-statement library and repository searches found no duplicate of this specialization.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/QuotientTwistBlindness.quotient_twist_blindness`
- Dependency: [D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality](CoordinateRestrictionNaturality.md)
