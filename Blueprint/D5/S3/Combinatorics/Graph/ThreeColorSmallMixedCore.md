# Small mixed-population certificate

## Abstract

A reciprocal population inequality is at least two when three mixed color populations have total between two and five and satisfy the empty-side incidence constraints.

**Theorem 1.1 (Bounded mixed-population inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorSmallMixedCore.small_population_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorSmallMixedCore.small_population_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m(i) be three natural mixed populations and x(i,j) the six ordinary populations. Assume x(i,i)=0, the empty-side balance inequalities m(j)+x(j,i)≤m(i) whenever x(i,j)=0, and 2≤Σm≤5. Then the maximum of the attachment-charge and Cauchy expressions from ThreeColorIncidence is at least two.

After sorting the mixed populations, each opposite-side ordinary pair is represented by a canonical thin or full choice. When at least one directed ordinary entry is absent, clearing the positive common denominator reduces the claim to coefficient nonnegativity; the kernel checks every sorted mixed triple with total 2, 3, 4, or 5 and every allowed choice. When all six entries are positive, elementary pair and color-loss estimates prove the attachment-charge expression is at least two. The ordinary variables remain unrestricted natural numbers.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorSmallMixedCore.small_population_bound`
- Dependency: [D5/S3/Combinatorics/Graph/ColoredReciprocalDeletion](ColoredReciprocalDeletion.md)
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorIncidence](ThreeColorIncidence.md)
