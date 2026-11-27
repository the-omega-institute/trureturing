# Joint decoding in a flat orthogonal phase basis

## Abstract

A phase-basis POVM and a diagonal upper bound give the exact uniform guessing probability.

**Theorem 1.1 (The normalized phase measurement attains the upper bound).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordDecoding.isGreatest_phase`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordDecoding.isGreatest_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yonina C. Eldar, G. David Forney Jr. (2001). *On quantum detection and the square-root measurement*. DOI: [10.1109/18.915636](https://doi.org/10.1109/18.915636). URL: <https://arxiv.org/abs/quant-ph/0005132>.

*Commentary.*

On a nonempty finite index type of size N, the phase matrix has unit-modulus entries and its column Gram matrix is N times the identity. The profile t is coordinatewise nonnegative and its squared coordinates sum to one.

The ensemble is uniform and its vectors are the entrywise products of t with the phase rows. The rank-one effects of the normalized rows sum to the identity and attain (sum_i t_i)^2 / N. The diagonal with entries t_i times sum_l t_l dominates each state matrix. Trace pairing gives the same upper bound for every labelled POVM, including when profile entries vanish.

**Theorem 1.2 (Exact whole-word success for the binary Walsh ensemble).**

Lean statement: `D5/S3/Quantum/PureState/JointRecordDecoding.pGuess_coordinateRecord`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/JointRecordDecoding.pGuess_coordinateRecord` (`✓ std3`). ∎

*Citation.* Yonina C. Eldar, G. David Forney Jr. (2001). *On quantum detection and the square-root measurement*. DOI: [10.1109/18.915636](https://doi.org/10.1109/18.915636). URL: <https://arxiv.org/abs/quant-ph/0005132>.

*Commentary.*

For every finite list of overlaps in [0,1], the canonical binary record has joint guessing probability equal to the product of the factors (1 + sqrt(1 - s^2)) / 2. The Walsh signs are the irreducible characters of the finite abelian group of binary words. Eldar and Forney's geometrically uniform result gives the finite minimum-error measurement for this symmetry.

The Lean proof uses the explicit normalized Walsh POVM and a diagonal bound. Each coordinate can have overlap zero or one. The empty product has value one.

## References

- Truth anchor: `D5/S3/Quantum/PureState/JointRecordDecoding.isGreatest_phase`
- Truth anchor: `D5/S3/Quantum/PureState/JointRecordDecoding.pGuess_coordinateRecord`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/Subentropy/GuessingProbability](../Subentropy/GuessingProbability.md)
