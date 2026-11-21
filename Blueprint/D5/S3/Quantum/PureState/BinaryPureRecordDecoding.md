# Joint decoding of binary pure records

## Abstract

Independent fair binary pure records have an attained joint guessing optimum on their original product carrier.

**Theorem 1.1 (Exact full-word guessing probability on the original carrier).**

Lean statement: `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.pGuess_coordinateProductRecord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.pGuess_coordinateProductRecord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, G. David Forney Jr. (2001). *On quantum detection and the square-root measurement*. DOI: [10.1109/18.915636](https://doi.org/10.1109/18.915636). URL: <https://arxiv.org/abs/quant-ph/0005132>.

*Commentary.*

At each position choose an independent fair bit and encode it using a normalized pair of vectors on that position’s finite carrier. The joint density state is the rank-one state of the product of these amplitudes.

For each coordinate let s be the modulus of its pair’s overlap. The maximum whole-word success is the product of (1 + sqrt(1 - s^2)) / 2 over all coordinates. Partial isometries identify the occupied subspaces, including one-dimensional spans. The empty word has success one.

**Theorem 1.2 (A full-carrier joint POVM attains the optimum).**

Lean statement: `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.isGreatest_pGuess_productRecord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.isGreatest_pGuess_productRecord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, G. David Forney Jr. (2001). *On quantum detection and the square-root measurement*. DOI: [10.1109/18.915636](https://doi.org/10.1109/18.915636). URL: <https://arxiv.org/abs/quant-ph/0005132>.

*Commentary.*

For repeated copies of a common normalized pair, the guessing probability is the greatest element of the actual success set. An attaining family of positive semidefinite matrices sums to the identity on the original product carrier. The greatest-element property bounds the success of every joint POVM on that carrier.

## References

- Truth anchor: `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.isGreatest_pGuess_productRecord`
- Truth anchor: `D5/S3/Quantum/PureState/BinaryPureRecordDecoding.pGuess_coordinateProductRecord`
- Dependency: [D5/S3/Quantum/PureState/JointRecordTransport](JointRecordTransport.md)
