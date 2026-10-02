# Monster Cubic Tensor Norm

## Abstract

The Norton trace Gram coefficient fixes the normalized cubic tensor Frobenius square sum.

**Theorem 1.1 (Symmetric trace Gram square sum).**

Lean statement: `D5/S3/VertexAlgebra/MonsterTensorNorm.symmetric_trace_gram_square_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterTensorNorm.symmetric_trace_gram_square_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert L. Griess Jr. (1981). *A construction of F1 as automorphisms of a 196,883-dimensional algebra*. DOI: [10.1073/pnas.78.2.689](https://doi.org/10.1073/pnas.78.2.689).

*Commentary.*

For a finite family of real symmetric square matrices, if every diagonal trace of T_i squared equals c, then the coordinate Frobenius square sum is the cardinality of the index type times c. The proof expands the trace and uses symmetry to turn each entry product into a square.

**Theorem 1.2 (Moonshine tensor numerical square sum).**

Lean statement: `D5/S3/VertexAlgebra/MonsterTensorNorm.moonshine_tensor_square_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterTensorNorm.moonshine_tensor_square_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert L. Griess Jr. (1981). *A construction of F1 as automorphisms of a 196,883-dimensional algebra*. DOI: [10.1073/pnas.78.2.689](https://doi.org/10.1073/pnas.78.2.689).

*Commentary.*

Specializing the finite family to dimension 196883 and the Norton coefficient 4620 - 2/3 gives the exact value 2728404614/3. The trace and symmetry hypotheses are inputs from the cited Norton formula; this declaration does not construct a VOA or claim a numerical stability constant for the actual Moonshine tensor.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterTensorNorm.moonshine_tensor_square_sum`
- Truth anchor: `D5/S3/VertexAlgebra/MonsterTensorNorm.symmetric_trace_gram_square_sum`
