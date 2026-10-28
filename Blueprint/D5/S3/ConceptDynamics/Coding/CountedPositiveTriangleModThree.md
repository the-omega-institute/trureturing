# The actual numbered-path triangle modulo three

## Abstract

CountedPositiveTriangleModThree

**Theorem 1.1 (Reduce arbitrary signed translation using a supplied period).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.periodic_translate_residue`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.periodic_translate_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a path fixed after d forward steps, with d nonzero, translation by any integer q equals forward iteration by its residue timeIndex q below d. The path need not have least period d. This identifies signed translation with the finite forward-shift convention.

**Theorem 1.2 (Parallel-edge relabelings have zero total reduced offset).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.parallel_edge_offset_sum_three_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.parallel_edge_offset_sum_three_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero period divisible by three, a vertex-fixing permutation of the actual parallel edges has total forward offset zero after reduction to ZMod 3. Individual orbit phases need not vanish. The relabel discrepancy argument uses this total cancellation.

**Theorem 1.3 (The actual numbered-path triangle modulo three).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.relativeForwardGyration_positive_triangle_mod_three`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.relativeForwardGyration_positive_triangle_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural dimensions n,m,p, count matrices R:n by m, U:m by p and V:p by n, and every nonzero period d divisible by three, the sum of the two actual relative forward gyrations for (R,U V) and (U,V R) equals that for (R U,V) after the quotient ZMod d to ZMod 3. Dimensions may vanish and edge fibers may be empty. The source orbit is the quotient of paths of actual minimal shift period d, with the inherited least-numbered-word representative.

The internal path coding preserves the forward shift. Its canonical image equals the translated target representative at the signed time minus the least-rotation index. Signed-time reduction on a periodic path and uniqueness below the minimal period prove that forward offsets add under composition. Reindexing the finite orbit sum by the induced basis equivalence makes gyration additive.

An endpoint-preserving edge bijection is a family of permutations of the actual numbered parallel-edge fibers. Finite induction over endpoint pairs and generation of each finite symmetric group by transpositions reduce its mod-three gyration to an involution. Additivity makes twice that value zero; two is invertible modulo three, so it vanishes.

The two canonical numberings of three half-edges define an endpoint-preserving associator. The exact recoding diagram contains three such associators, interspersed with the two elementary recodings. Splitting the actual edge at adjacent times and rejoining verifies this diagram. Their mod-three gyrations vanish, leaving the claimed triangle. This is the classical orbit-cocycle and transposition-generation argument on the specified numbered graph; it is not a claim of mathematical novelty.

Only the mod-three quotient is asserted. This gives neither the full mod-six sign law, nor image exhaustion, nor the original-h SGCC or FixT6 completion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.parallel_edge_offset_sum_three_zero`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.periodic_translate_residue`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleModThree.relativeForwardGyration_positive_triangle_mod_three`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration](CountedOriginalOrbitGyration.md)
