# Two uniform subentropy values

## Abstract

The exact subentropy values of the uniform two-level and four-level density matrices.

The index type may be any finite type with decidable equality of the stated cardinality. The diagonal entries are real scalars embedded in the complex field. Both values follow by algebraic expansion of the determinant kernel and the corresponding absolutely convergent improper scalar integrals.

**Theorem 1.1 (The maximally mixed qubit).**

Lean statement: `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformTwo`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformTwo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

If the cardinality is two, Q(I/2)=log 2−1/2. For t>0 its kernel equals 1/(t+1/2)−1/(t+1)−1/(4(t+1/2)^2).

**Theorem 1.2 (The maximally mixed four-level state).**

Lean statement: `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformFour`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

If the cardinality is four, Q(I/4)=log 4−13/12. For t>0 its kernel equals 1/(t+1/4)−1/(t+1)−3/(8(t+1/4)^2)+1/(16(t+1/4)^3)−1/(256(t+1/4)^4). These two values determine the exact positive gap of the Bell-pair strong-subadditivity counterexample.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformFour`
- Truth anchor: `D5/S3/Quantum/Subentropy/UniformValues.subentropy_uniformTwo`
- Dependency: [D5/S3/Quantum/Subentropy/Basic](Basic.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformIntegrals](UniformIntegrals.md)
