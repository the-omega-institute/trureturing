# Constant Potential on a Restricted Prefix Tree

## Abstract

An explicit finite-word probability has constant matching-prefix potential on a restricted tree.

**Theorem 1.1 (A normalized recursive law with equal potential at every admissible word).**

Lean statement: `D5/S3/Arith/Congruence/RestrictedSpineConstantPotential.restricted_spine_constant_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/RestrictedSpineConstantPotential.restricted_spine_constant_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite alphabet, one distinguished symbol, and a set of side symbols that excludes it. A word is admissible when it consists entirely of the distinguished symbol, or its first different symbol belongs to the side set; the remaining suffix is unrestricted. Assign an arbitrary positive real weight to each depth. The kernel is one plus the sum of these weights along the matching prefix of the target word and the test word.

The theorem constructs test-word weights recursively. At each distinguished node, each side child receives a share inversely proportional to its uniform-suffix potential plus the next depth weight; the continuing child receives the corresponding share for its restricted suffix. The common multiplier is the inverse sum of these reciprocal costs. After entering a side child, the remaining symbols are uniform.

These weights are nonnegative, sum to one, vanish outside the admissible words, and give the same expected kernel value at every admissible target. The value is given by the explicit harmonic recursion in the statement. The proof simultaneously establishes the uniform suffix identities and the restricted identities by induction on the list of depth weights. Empty words and an empty side set are included.

For prime-power digits, choosing depth weights 3, 5, 7 and so on gives the squared coherent-prefix load used in the star-family obstruction to a universal Gamma73 head bound. This theorem establishes the general finite-tree probability construction. Its residue-digit embedding, the actual forbidden-family decomposition, the numerical threshold and the full covering problem are separate obligations; it does not settle Erdős #7.

## References

- Truth anchor: `D5/S3/Arith/Congruence/RestrictedSpineConstantPotential.restricted_spine_constant_potential`
