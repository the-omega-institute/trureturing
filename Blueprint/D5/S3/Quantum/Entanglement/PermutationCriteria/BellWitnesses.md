# Bell witness coordinate kernels

## Abstract

Which correlated basis bits survive in each row or column string of a tensor-index permutation.

**Definition 1.1 (A row or column position).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sidePos`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sidePos` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean side and a party k, sidePos is the ket position when side is true and the bra position otherwise.

**Definition 1.2 (Selection of one matrix side).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideSelected`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideSelected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A flat position is selected when it is even for side true, or odd for side false.

**Definition 1.3 (A reshaped correlated string).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage`

*Formalization.* `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose a set S of parties, one row bit and one column bit. Form the corresponding two basis strings, interleave them, pull them back by the inverse permutation, and project onto the selected output side.

**Theorem 1.4 (Exact bit kernel on either side).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every local dimension at least two, support set S, position permutation and selected side, two reshaped strings agree exactly when their first bits agree whenever any ket position from S lands on that side, and their second bits agree whenever any bra position from S lands on that side. Empty S and zero parties are allowed.

**Theorem 1.5 (The four permuted Bell entries).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.permute_bellWitness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.permute_bellWitness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all parties i,j, local dimension at least two and position permutation, the permuted Bell witness is the sum of the four matrix units indexed by its reshaped row and column strings, each with coefficient one half.

**Theorem 1.6 (The Bell separation values).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.bellWitness_traceNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.bellWitness_traceNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every local dimension at least two, parties i,j and permutation sigma, the permuted Bell witness has trace norm one, twice the square root of one half, or two according as the paired row-side labels of i,j have Hamming distance zero, one, or two. The statement also includes i equal to j, when the distance is zero.

**Theorem 1.7 (Dependence preserves paired-label distance).**

Lean statement: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.dependent_pairDistance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.dependent_pairDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two permutations have equal trace norms on every positive trace-one state in local dimension at least two, then the Hamming distance between the paired row-side labels of any two parties agrees for the two permutations. The three Bell norm values are distinct, so the Bell witness detects each of the three distances.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.bellWitness_traceNorm`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.dependent_pairDistance`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.permute_bellWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideImage_kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sidePos`
- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses.sideSelected`
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](BellBlocks.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses](Witnesses.md)
