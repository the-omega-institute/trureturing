# Finite Kraus Representations

## Abstract

Every finite rectangular completely positive matrix map has a finite Kraus witness.

Use the output-input order for the Choi coordinates: the channel acts on the first factor of the unnormalized maximally entangled projector. The finite Kraus family has rectangular output-by-input matrices; the zero map is included. Trace preservation is equivalent to the sum of the adjoint-Kraus products being the identity: cyclicity proves sufficiency, and testing every matrix unit proves necessity.

Ordinary transposition preserves positive matrices but is not completely positive. Its Choi matrix is the swap. On two qubits the partial transpose of the normalized Bell density is half the swap, with three eigenvalues equal to one half and one equal to minus one half. The antisymmetric vector detects the negative direction. Positivity on inputs alone therefore does not replace positivity with every auxiliary interface.

**Theorem 1.1 (Complete positivity gives a rectangular Kraus family).**

$$\operatorname{IsCompletelyPositive}(Phi) \Rightarrow \exists M, Phi=\operatorname{ofKraus}(M,M).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

For finite coordinate types A and B with decidable equality and an RCLike scalar, every completely positive rectangular MatrixMap Φ has a witness family M indexed by B × A and equals the associated Kraus sum (ofKraus denotes the Lean function of_kraus). This is a CP representation statement; it does not assert trace preservation.

The declaration is the selected upstream Physlib result at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260, routed from QuantumInfo/Channels/MatrixMap.lean and Unbundled.lean. Finite and decidable assumptions are retained explicitly.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](FiniteKrausChannel.md)
