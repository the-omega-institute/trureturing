# Coordinate Restriction Naturality

## Abstract

Coordinate restriction preserves twisted diagonals for compatible value maps.

**Theorem 1.1 (Coordinate restriction commutes with twisted diagonalization).**

$$\forall A_{i}, A_{j}, Y_{i}, Y_{j}: \operatorname{Type},\ \forall iota: \operatorname{Embedding}\left(A_{i}, A_{j}\right), q: Y_{j} \to Y_{i},\ tau_{j}: Y_{j} \to Y_{j}, tau_{i}: Y_{i} \to Y_{i},\ E: A_{j} \to \left(A_{j} \to Y_{j}\right),\ (q \circ tau_{j} = tau_{i} \circ q) \Rightarrow \operatorname{restrictVector}\left(iota, q, \operatorname{diagonal}\left(tau_{j}, E\right)\right) = \operatorname{diagonal}\left(tau_{i}, \operatorname{restrictTable}\left(iota, q, E\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality.coordinate_restriction_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Ai and Aj be address types, Yi and Yj be value types, iota embed Ai into Aj, and q map Yj to Yi. Restrict a table E by sending (a,b) to q(E(iota(a),iota(b))), and restrict a vector u by sending a to q(u(iota(a))).

For twists tauJ on Yj and tauI on Yi, assume q after tauJ equals tauI after q. Then restricting the tauJ-twisted diagonal of every table E equals the tauI-twisted diagonal of the restricted table. The proof evaluates the imported semiconjugacy equivalence at each diagonal entry.

Loogle and LeanSearch found Function.semiconj_iff_comp_eq for the exact intertwining hypothesis, and the Lean proof imports and applies it. Neither search found the full coordinate-restriction statement; repository and digestion-record searches found no duplicate.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality.coordinate_restriction_naturality`
- Dependency: [D5/S0/Diagonal/EscapeCount](../EscapeCount.md)
