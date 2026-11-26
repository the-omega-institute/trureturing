# Position masses and their Cesàro limits

## Abstract

The pointwise position averages give probability laws at every finite dimension.

**Theorem 1.1 (Real-horizon continuous-time average).**

$$\frac{1}{T} \int_{0}^{T} p_{C}(t,x) dt \to \overline{p}_{C}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages.tendsto_continuousAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

The CT position mass is the squared complex norm of the origin amplitude. T tends to infinity through real horizons. The limiting mass is the Walsh expansion with the pairwise equality indicator. Its masses are nonnegative and sum to one.

**Theorem 1.2 (Integer-horizon discrete-time average).**

$$\frac{1}{T} \sum_{n=0}^{T-1} p_{D}(n,x) \to \overline{p}_{D}(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages.tendsto_discreteAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

The DT mass sums the squared complex norms over the coin, as checked by discreteMass_eq_complex. T tends to infinity through natural horizons. The limiting masses also form a probability law. Walsh orthogonality reduces each character observable to ordered pairs (a,a XOR c).

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages.tendsto_continuousAverage`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/PositionAverages.tendsto_discreteAverage`
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk](Walk.md)
