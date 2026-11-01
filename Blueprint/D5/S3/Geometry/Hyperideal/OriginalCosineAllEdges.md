# Six original cosine bounds

## Abstract

Six target-edge original cosine bounds share one determinant sign.

Fix the local edge order `(12,13,14,34,24,23)` and six coordinates `(r,a,b,o,c,d)`, all greater than one. For one ordered tuple, `strictCosine` is the conjunction
\[
-1 < \frac{N}{\sqrt{D_1}\sqrt{D_2}} < 1.
\]
The six target tuples are `(r,a,b,o,c,d)`, `(a,r,b,c,o,d)`, `(b,r,a,d,o,c)`, `(o,a,d,r,c,b)`, `(c,r,d,a,o,b)`, and `(d,r,c,b,o,a)`.

The determinant identity for each tuple is the existing `OriginalCosineDeterminantInterface` identity. The corresponding vertex relabeling simultaneously permutes rows and columns, so every transformed Gram determinant equals the original determinant. Positivity of `D1` and `D2` follows from the six coordinates being greater than one; the square-root interval calculation is carried out over the reals.

This module closes the finite algebraic six-edge criterion only. It does not assert a hyperideal geometric realization, a compatible global face pairing, or any statement about the unresolved transport and gluing clauses.

**Theorem 1.1 (Common determinant criterion).** For all six coordinates greater than one,
\[
\det G<0 \Longleftrightarrow
\bigwedge_{e\in\{r,a,b,o,c,d\}} -1<\varphi_e<1.
\]

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg`
- Dependency: `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface`
