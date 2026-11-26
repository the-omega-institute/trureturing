# Shifted moments and weak convergence on the unit interval

## Abstract

The fixed-order shifted moments determine convergence of probability laws on [0,1].

**Theorem 1.1 (Existence of a weak limit).**

$$(\exists \pi, \mu_{i} \to \pi) \iff \forall k>0, \exists m, M_{k}(\mu_{i}) \to m$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/WeakLimits.exists_weakLimit_iff_shiftedMoments_converge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yusuke Ide, Norio Konno, Shuhei Mano (2026). *Scaling Limits of Time-averaged Distributions for Symmetric Quantum Walks on Hypercubes*. DOI: [10.48550/arXiv.2611.31635](https://doi.org/10.48550/arXiv.2611.31635). URL: <https://arxiv.org/abs/2611.31635v1>.

*Commentary.*

For a family of probability measures on [0,1] along a filter, M_k is the integral of (1−2x)^k. Stone–Weierstrass gives density of polynomials in the shifted coordinate. The moment map into the product of real lines is a continuous closed embedding by compactness and moment separation. Along a nontrivial filter, coordinate convergence therefore gives a weak limit, and weak convergence gives convergence of each coordinate. Along the bottom filter, every convergence statement holds and a Dirac probability at 0 witnesses existence.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/WeakLimits.exists_weakLimit_iff_shiftedMoments_converge`
