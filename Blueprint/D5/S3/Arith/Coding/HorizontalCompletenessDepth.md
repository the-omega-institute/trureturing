# Horizontal Completeness Depth

## Abstract

Joint residues modulo an initial prime segment separate a bounded natural interval exactly when the segment's modulus product exceeds the interval, and the first such segment is its horizontal completeness depth.

**Lemma 1.1 (Prime-prefix residues separate exactly below their product).**

$$\forall N, r \in \mathbb{N}, \operatorname{InjOn}\left(\operatorname{residueReading}\left(r\right), [0, N]\right) \iff N < \operatorname{primePrefixProduct}\left(r\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/HorizontalCompletenessDepth.residue_reading_injOn_iff_primorial_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The depth-r reading records a natural number modulo each of the first r primes. On the interval from zero through N, this joint reading is injective exactly when the product of those primes is greater than N; the empty prefix is included with product one.

If the product is at most N, zero and the positive prefix product are distinct points of the interval with the same residue in every coordinate. Conversely, equality of all coordinates and pairwise coprimality give congruence modulo the entire product, and two numbers below that product with this congruence must coincide.

**Lemma 1.2 (Some prime-prefix product exceeds every natural bound).**

$$\forall N \in \mathbb{N}, \exists r \in \mathbb{N}, N < \operatorname{primePrefixProduct}\left(r\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/HorizontalCompletenessDepth.exists_primePrefixProduct_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural bound N is exceeded by the product of some finite initial segment of the primes. The proof chooses the segment of length N: each of its prime factors is at least two, so its product is at least 2 to the N, which is strictly greater than N.

This existence result makes the least successful depth well-defined for every bounded natural interval, including the zero bound.

**Theorem 1.3 (Horizontal depth is the least faithful prime-residue depth).**

$$\forall N \in \mathbb{N}, \operatorname{IsLeast}\left(\{r \in \mathbb{N} \mid \operatorname{InjOn}\left(\operatorname{residueReading}\left(r\right), [0, N]\right)\}, \operatorname{horizontalDepth}\left(N\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/HorizontalCompletenessDepth.horizontal_completeness_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each N, horizontalDepth N is the least number of initial prime coordinates whose joint residue reading is injective on the natural interval from zero through N.

The depth is defined as the first prime-prefix product greater than N. The injectivity threshold identifies that same condition with faithfulness on the interval, so the selected depth is faithful and no smaller faithful depth can exist.

## References

- Truth anchor: `D5/S3/Arith/Coding/HorizontalCompletenessDepth.exists_primePrefixProduct_gt`
- Truth anchor: `D5/S3/Arith/Coding/HorizontalCompletenessDepth.horizontal_completeness_depth`
- Truth anchor: `D5/S3/Arith/Coding/HorizontalCompletenessDepth.residue_reading_injOn_iff_primorial_gt`
