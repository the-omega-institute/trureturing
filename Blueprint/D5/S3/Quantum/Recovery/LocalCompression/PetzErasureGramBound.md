# Gram bound for complete erasure

## Abstract

The squared joint and marginal roots control the orthogonal population of the ordinary Petz benchmark.

For a rank-one retained likelihood, the ordinary Petz benchmark uses the first column of the joint square root. Its component orthogonal to the corresponding marginal column is measured by the Gram numerator below.

**Theorem 1.1 (Block traces of the squared joint root).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.traceBlocks_root_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.traceBlocks_root_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal partial traces are Hilbert–Schmidt norm squares. The lower off-diagonal trace is Tr((A + C)B).

**Theorem 1.2 (Hilbert-space Gram estimate).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.gram_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.gram_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal norm identities and the off-diagonal pairing bound the residual by (a² + ac)δ in squared norm.

**Theorem 1.3 (Gram bound with the actual partial trace).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.matrix_gram_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.matrix_gram_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the partial trace of the squared joint root equals the square of the qubit root, the defect δ = ‖B‖² − |b|² is nonnegative and ‖aB − bA‖² ≤ (a² + ac)δ.

**Theorem 1.4 (Orthogonal population from the benchmark Gram).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.benchmark_orthogonal_numerator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.benchmark_orthogonal_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the Gram of the first joint-root block column on (−conj b, a) gives the numerator ‖aB − bA‖².

**Theorem 1.5 (Sharp quadratic coefficient).**

Lean statement: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.quadratic_coefficient_isLeast`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.quadratic_coefficient_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least coefficient relative to a² + c² on the nonnegative quadrant is (1 + √2)/2.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.benchmark_orthogonal_numerator`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.gram_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.matrix_gram_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.quadratic_coefficient_isLeast`
- Truth anchor: `D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound.traceBlocks_root_mul`
