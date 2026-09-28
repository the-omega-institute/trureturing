# Finite Kraus Representations

## Abstract

Every finite rectangular completely positive matrix map has a finite Kraus witness.

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
