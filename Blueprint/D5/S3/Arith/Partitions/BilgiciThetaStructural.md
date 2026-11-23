# Structural quartic factorization

## Abstract

Structural quartic factorization.

**Theorem 1.1 (The full weight component factors by the cubic).**

$$\exists\,Q\in\mathbb{F}_{19}[Z_{1},...,Z_{9}],\quad Q=Q_{{str}} \land Q\neq0 \land \operatorname{Homogeneous}(Q,4) \land \operatorname{WeightedHomogeneous}(Q,w,9) \land [BC^{3}]_{11}-S_{Z}Q\in\mathcal{I}_{\theta} \land \overline{Q}\neq0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaStructural.structural_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

The literal weight component lies in the joint kernel. Trace coefficients in degrees 30 and 49 recover the quotient class of its quartic cofactor from the projections of 6799 and 3689. The resulting polynomial is Q_str. The first trace coefficient is one in degree 30, so the cofactor has a nonzero class.

## References

- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaStructural.structural_factorization`
- Dependency: [D5/S3/Arith/Partitions/BilgiciThetaJointKernel](BilgiciThetaJointKernel.md)
- Dependency: [D5/S3/Arith/Partitions/BilgiciThetaLiteralTests](BilgiciThetaLiteralTests.md)
