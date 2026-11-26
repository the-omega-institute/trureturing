# The sharp five-dimensional two-basis score

## Abstract

The exact maximum of the dimension-five computational and Fourier two-ray score is (14 + 2√5)/5, attained by Qian's orthonormal pair.

**Theorem 1.1 (Sharp upper bound for the Born laws).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.fiveScore_le_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.fiveScore_le_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

For arbitrary complex unit vectors x and y, sum (p−q)²/(p+q) over the computational and inverse Fourier Born outcome tables, taking a common zero row to contribute zero. The score is at most (14 + 2√5)/5. At or above the proposed cutoff every compatible sign mask is a critical balanced mask. Affine covariance reduces it to centered geometry. The weighted residual separates into reflection-even and odd terms, and the certified estimates absorb the overlap mismatch within the joint Rayleigh deficit.

**Theorem 1.2 (Sharp upper bound in Qian's convention).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.positiveFourierScore_le_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.positiveFourierScore_le_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

Simultaneous complex conjugation preserves the norm and transports the inverse Fourier probabilities to the positive normalized Fourier convention of Eq. (9). The upper bound thus holds for all unit pairs, including Qian's orthonormal family.

Qian's Theorem 6.14 and Eqs. (33)–(36) give an orthonormal pair attaining (14 + 2√5)/5. The upper bound together with that previously proved attainment identifies the same maximum for arbitrary unit pairs and for orthonormal pairs.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.fiveScore_le_sharp`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn.positiveFourierScore_le_sharp`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows](SharpRows.md)
