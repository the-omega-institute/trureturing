# The origin-started walks in Walsh coordinates

## Abstract

The source CT matrix and complex DT evolution agree with their Walsh expansions.

**Theorem 1.1 (Continuous-time origin amplitude).**

$$\psi_{C}(t,x) = s \sum_{a} b_{a}(x) \exp(i(\rho_{a}-1)t)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk.continuousState_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

The source evolution in §3, printed p. 4, equation (10), is exp(−it(I−P)). Its origin column is the amplitude. The transition entry is p(x XOR z). The normalized Walsh vector b_a(x) is s times the character at a and s = 2^(−d/2). The factor s outside the sum is its value at the origin.

**Theorem 1.2 (Complex coined evolution).**

$$\psi_{D}(n,y,x) = v(n,y,x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk.discreteComplexState_eq_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

The right side is the real-coordinate state included in the complex numbers. The complex recurrence sums C(y,z) ψ(n,z,x XOR y) over z, with C(y,z) = 2√p(y)√p(z) − 1_{y=z}. Its initialization is 1_{x=0}√p(y). This is the shift after reflection in §4.2, printed p. 7. The equality is proved at every n, y and x.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk.continuousState_fourier`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk.discreteComplexState_eq_ofReal`
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages](CoinAverages.md)
