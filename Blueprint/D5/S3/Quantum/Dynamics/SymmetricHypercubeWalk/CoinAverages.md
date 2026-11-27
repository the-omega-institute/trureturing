# Time averages of two Walsh blocks

## Abstract

The coin orbit is a plane rotation at interior eigenvalues and a one-dimensional phase at the endpoints.

**Theorem 1.1 (Rotation of the initial coin).**

$$v_{a}(n) = \operatorname{cos}(n\theta) s + \operatorname{sin}(n\theta) e$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages.orbit_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

In character a, θ = arccos(ρ(a)), s is the unit vector with entries √p(y), and e is the signed coin vector with its component along s removed and divided by √(1 − ρ(a)²). When ρ(a) = ±1, the direction e is zero and the state is ρ(a)ⁿ s.

**Theorem 1.2 (The discrete-time pair mean).**

$$A_{T}(a,b) \to D(a,b)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages.tendsto_discretePair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

Here A_T is the average coin inner product of the two orbits over n = 0, …, T−1. For unequal numerical eigenvalues the mean is zero. Equal endpoints contribute one. Equal interior eigenvalues r contribute half of 1 plus (ρ(a XOR b) − r²)/(1 − r²). The continuous-time phase mean is the indicator of equality of the two eigenvalues. The difference lies in [0,1], including the endpoint cases.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages.orbit_rotation`
- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages.tendsto_discretePair`
