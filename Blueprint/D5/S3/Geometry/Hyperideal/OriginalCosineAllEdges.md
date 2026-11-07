# Six original cosine bounds

## Abstract

Six target-edge original cosine bounds share one determinant sign.

Fix the local edge order (12,13,14,34,24,23) and six coordinates (r,a,b,o,c,d), all greater than one. For one ordered tuple, strictCosine is the conjunction -1 < N/(sqrt(D1*D2)) and N/(sqrt(D1*D2)) < 1. The six target tuples are (r,a,b,o,c,d), (a,r,b,c,o,d), (b,r,a,d,o,c), (o,a,d,r,c,b), (c,r,d,a,o,b), and (d,r,c,b,o,a).

The determinant identity for each tuple is the existing OriginalCosineDeterminantInterface identity. The corresponding vertex relabeling simultaneously permutes rows and columns, so every transformed gram determinant equals the original determinant. Positivity of D1 and D2 follows from the six coordinates being greater than one; the square-root interval calculation is carried out over the reals.

This module closes the finite algebraic six-edge criterion only. It does not assert a hyperideal geometric realization, a compatible global face pairing, or any statement about the unresolved transport and gluing clauses.

**Theorem 1.1 (Common determinant criterion).**

$$\left(\left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{gram}\left(r, a, b, o, c, d\right)\right) < 0 \Leftrightarrow \left(\left(\left(\left(\left(\operatorname{strictCosine}\left(r, a, b, o, c, d\right) \land \operatorname{strictCosine}\left(a, r, b, c, o, d\right)\right) \land \operatorname{strictCosine}\left(b, r, a, d, o, c\right)\right) \land \operatorname{strictCosine}\left(o, a, d, r, c, b\right)\right) \land \operatorname{strictCosine}\left(c, r, d, a, o, b\right)\right) \land \operatorname{strictCosine}\left(d, r, c, b, o, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common signed Gram determinant is negative exactly when all six target-edge original cosines lie strictly between -1 and 1.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg`
- Dependency: [D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface](OriginalCosineDeterminantInterface.md)
