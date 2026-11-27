# DoubleStarNativeGram

## Abstract

Negative native hyperideal Gram determinants for the three local transition families.

Negative native hyperideal Gram determinants for the three local transition families.

These are exact local real inequalities only. Physical realization, seed-parameter existence, face identifications, compatible global gluing, boundary angle budgets and a global cap remain outside these statements. No general CFMP open problem is claimed solved.

**Theorem 1.1 (chosenOpp native gram negative).**

Lean statement: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.chosenOpp_native_gram_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.chosenOpp_native_gram_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion.

**Theorem 1.2 (first native gram negative).**

Lean statement: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion.

**Theorem 1.3 (middle native gram negative).**

Lean statement: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion.

**Theorem 1.4 (last native gram negative).**

Lean statement: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact local statement; consult the linked Lean declaration for all hypotheses and the precise conclusion.

## Six original cosine bounds for the double star

For a real tuple (r,a,b,o,c,d) in edge order (12,13,14,34,24,23), write Q(r,a,b,o,c,d) = N(r,a,b,o,c,d) / (sqrt(D1(r,a,d)) * sqrt(D2(r,b,c))). The signed Gram matrix and the functions N, D1 and D2 are those of `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface`.

Assume r, a, b, o, c and d are each strictly greater than 1 and det(gram(r,a,b,o,c,d)) < 0. Then −1 < Q < 1 for each of the six argument tuples, in order (r,a,b,o,c,d), (a,r,b,c,o,d), (b,r,a,d,o,c), (o,a,d,r,c,b), (c,r,d,a,o,b) and (d,r,c,b,o,a). Apply the determinant-to-cosines direction of `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg`.

For every real x with 12 ≤ x ≤ 20, the six inequalities hold for each tuple below. In every tuple r = x, so r > 1, and all four fixed entries exceed 1. The proved opposite-root lower bounds supply o > 1, and the corresponding native Gram theorems supply the negative determinant.

First family. Use (x,101/100,500,o,101/100,3/2) with o = chosenOpp(x,101/100,3/2,500,101/100). The root satisfies 6 < o < 30, and the native determinant is negative. `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.first_exact`, `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative`

Middle family. Use (x,500,500,o,101/100,101/100) with o = chosenOpp(x,500,101/100,500,101/100). The root satisfies 6 < o < 250, and the native determinant is negative. `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.middle_exact`, `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative`

Last family. Use (x,500,101/100,o,101/100,101/100) with o = chosenOpp(x,500,101/100,101/100,101/100). The root satisfies 2 < o < 6, and the native determinant is negative. `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.last_exact`, `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative`

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.chosenOpp_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.first_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.last_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarNativeGram.middle_native_gram_negative`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.first_exact`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.last_exact`
- Truth anchor: `D5/S3/Geometry/Hyperideal/DoubleStarOpposite.middle_exact`
- Truth anchor: `D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.all_edges_strict_iff_det_neg`
- Dependency: [D5/S3/Geometry/Hyperideal/DoubleStarOpposite](DoubleStarOpposite.md)
- Dependency: [D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface](OriginalCosineDeterminantInterface.md)
- Narrative reference: [D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface](OriginalCosineDeterminantInterface.md)
