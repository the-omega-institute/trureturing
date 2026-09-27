# The minimum depth of open integrable circuits

## Abstract

For the open-boundary integrable quantum circuits of Garcia Fernandez, Paletta and Retore, the least depth over the configurations with kappa of the N sites carrying -kappa is floor(N/(kappa + 1)) + 1 whenever 1 <= kappa and 2 kappa <= N.

**Theorem 1.1 (Minimum depth).**

$$\forall N \in \mathbb{N},\; \forall kappa \in \mathbb{N},\; (1 \le kappa \land 2 \cdot kappa \le N) \Rightarrow (\operatorname{minDepth}\left(N, kappa\right) = \left\lfloor\frac{N}{kappa + 1}\right\rfloor + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Miguel Garcia Fernandez, Chiara Paletta, Ana L. Retore (2026). *Open-boundary integrable quantum circuits with different geometries*. DOI: [10.48550/arXiv.2607.02093](https://doi.org/10.48550/arXiv.2607.02093). URL: <https://arxiv.org/abs/2607.02093v1>.

*Commentary.*

Read the circuit of a set S of sites as the path of sites 0, 1, ..., N, with site 0 for the boundary gate K1, site N for KN and site k in between for U_k: the circuit lists these gates in the order of the sites outside S decreasing, then 0, then the sites of S increasing, and two gates share a site of the chain exactly when their sites are consecutive. So the circuit fits in L layers exactly when some labelling of the sites 0, ..., N by numbers below L increases along each step from k to k + 1 with k + 1 in S and decreases along each other step. Along a run of consecutive steps outside S the labels decrease, and each of the |S| steps into S can raise the label by at most L - 1, which forces N < (|S| + 1) L; hence the depth is at least floor(N/(kappa + 1)) + 1. Conversely, cutting the sites 1, ..., N into kappa + 1 runs of length at most floor(N/(kappa + 1)) separated by the kappa sites of S gives a labelling below floor(N/(kappa + 1)) + 1, by induction on kappa.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OpenIntegrableCircuitMinDepth.result`
- Dependency: [D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation](OpenIntegrableCircuitDepthRefutation.md)
