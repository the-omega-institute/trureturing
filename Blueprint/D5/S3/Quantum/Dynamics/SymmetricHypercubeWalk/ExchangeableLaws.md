# Exchangeable cube laws and shifted radial moments

## Abstract

At fixed order, a finite sampling estimate identifies a Walsh coefficient with a shifted moment up to vanishing error.

**Theorem 1.1 (The sampling error bound).**

$$\lvert W_{c}(\mu)-M_{k}(\nu)\rvert \leq \frac{k(k-1)}{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws.abs_walshCoefficient_sub_shiftedMoment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

Let μ be permutation-invariant on the d-cube, let ν be its normalized Hamming-weight pushforward, and let c embed k coordinates. The coefficient W_c is the expected product of the k coordinate signs. Sampling without replacement computes this same expectation by exchangeability. Sampling with replacement computes M_k(ν). A collision union bound gives k(k−1)/d. For fixed k the corresponding bound for a difference of two laws is twice this quantity. At d = 0 the embedding forces k = 0, both observables are one, and the bound uses Lean’s convention that division by zero is zero.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws.abs_walshCoefficient_sub_shiftedMoment_le`
- Dependency: [D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/WeakLimits](WeakLimits.md)
