# Krawtchouk eigenvalues and finite Walsh coefficients

## Abstract

The shell profile determines the CT collision coefficient and the CT-minus-DT gap.

**Theorem 1.1 (Eigenvalue at a Walsh character).**

$$\rho_{k} = \sum_{h=0}^{d} w_{h} K_{h}(k)/N_{h}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.eigen_eq_krawtchouk` (`✓ std3`). ∎

*Citation.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

Here k is the Hamming weight of the character and N_h = choose(d,h). The weights are nonnegative and sum to one over 0 ≤ h ≤ d. An increment of weight h has mass w_h/N_h. The Krawtchouk polynomial K_h(k) sums (−1)^j choose(k,j) choose(d−k,h−j) over j = 0, …, min(h,k). This is the eigenvalue in §2.2, printed p. 4, equation (8).

**Theorem 1.2 (The finite CT-minus-DT coefficient).**

$$\mathbb{E}_{A_{C,d}}[c] - \mathbb{E}_{A_{D,d}}[c] = W_{d,k}(g)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.finite_shell_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

A_{C,d} and A_{D,d} are the CT and DT position Cesàro laws. The expectations evaluate the Walsh character c of weight k ≤ d. The normalized sum W_{d,k}(f) counts (a,a XOR c). It is 2^(−d) times the sum over 0 ≤ i ≤ d−k and 0 ≤ j ≤ k, with weight choose(d−k,i) choose(k,j) on f(i+j,i+k−j). The summand g(u,v) is (1−ρ_k)/(2(1−ρ_u²)) for equal interior eigenvalues ρ_u = ρ_v and zero elsewhere. The gap is between zero and one.

**Theorem 1.3 (The finite CT collision coefficient).**

$$\mathbb{E}_{A_{C,d}}[c] = W_{d,k}(b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.finite_shell_collisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

The expectation evaluates the Walsh character c under the CT position Cesàro law A_{C,d}. The summand b(u,v) is 1 when ρ_u = ρ_v and 0 otherwise. It counts coincidences across different shells and both equal endpoints. The DT coefficient is the CT coefficient minus the gap in the preceding identity. The owner also proves both formulas as limits of the actual finite-horizon observables.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.eigen_eq_krawtchouk`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.finite_shell_collisions`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ShellCoefficients.finite_shell_gap`
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages](PositionAverages.md)
