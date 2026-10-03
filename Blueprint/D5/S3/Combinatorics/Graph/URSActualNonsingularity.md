# Nonsingularity of actual uniform reflection cross-Grams

## Abstract

Fix one indexed array of 2n permutation rows on n symbols. Its indicator matrices, fibres and joint counts all use the same rows. Pairwise commutation is an explicit additional hypothesis. No distinct-row or reduced-array hypothesis is imposed.

**Theorem 1.1 (Every actual off-diagonal cross-Gram has trivial real kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/URSActualNonsingularity.actual_crossGram_kernel_trivial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/URSActualNonsingularity.actual_crossGram_kernel_trivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be odd and at least three. Let rho index 2n permutations of Fin n, with every column-symbol fibre of cardinality two and reflected pair counts equal for distinct columns and distinct symbols. Assume all actual cross-Grams B(x) transpose times B(y) commute pairwise. For distinct columns u and v and a real symbol vector z, if H(u,v) times z is zero, then z is zero. H(u,v) is the actual real cross-Gram formed from those indicator matrices.

The actual support components partition the symbol set. The supplied biregular block relation and actual linking counts give a common odd component size d at least three, with all components of size d or twice d. Hence no component has cardinality divisible by four. A double entry would isolate a two-symbol component, so all off-diagonal entries are zero or one and every support vertex has two neighbors. The finite cycle theorem applies to this proved actual graph. Along its cycle the kernel equation gives z at position j plus two equal to minus z at position j; closing a cycle whose length is not divisible by four forces its coordinates to vanish.

The conclusion uses the explicit commutation hypothesis; fibre size and reflection alone are not asserted to imply it.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/URSActualNonsingularity.actual_crossGram_kernel_trivial`
- Dependency: [D5/S3/Combinatorics/Graph/URSComponentParity](URSComponentParity.md)
