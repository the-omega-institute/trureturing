# Divergence of the last site of the nearest-neighbor QES chain

## Abstract

The last site of the cyclic nearest-neighbor QES chain exceeds every fixed real bound for all sufficiently large chain lengths.

**Definition 1.1 (The last-site question).**

$$\operatorname{claim} \iff (\forall B \in \mathbb{R},\; \exists N0 \in \mathbb{N},\; \forall N \in \mathbb{N},\; (N0 \leq N \Rightarrow \forall xi \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (3 \leq N \Rightarrow \operatorname{StrictMono}\left(xi\right) \Rightarrow \operatorname{Sites}\left(xi\right) \Rightarrow B < xi\left(\langle N - 1 \rangle\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.claim` (`✓ std3`).

*Citation.* A. Enciso; F. Finkel; A. González-López; M. A. Rodríguez (2007). *A novel quasi-exactly solvable spin chain with nearest-neighbors interactions*. DOI: [10.1016/j.nuclphysb.2007.07.001](https://doi.org/10.1016/j.nuclphysb.2007.07.001). URL: <https://arxiv.org/abs/0704.3046v1>.

*Commentary.*

The paper asks in §2, printed p. 9, before Eq. (19): "It is also of interest to determine whether the position of the last spin tends to infinity as N → ∞, since according to our interpretation of the chain’s geometry the number 2ξN/π is the radius of the circle on which the spins lie." The displayed proposition expresses divergence uniformly over all strictly increasing solutions of the cyclic equations (6). The symbol xi denotes ξ : Fin N → ℝ; zero-based index N − 1 is the source's site ξN. Subtraction N − 1 is truncated natural subtraction. The notation ⟨N − 1⟩ denotes the Fin N index with its proof component suppressed; 3 ≤ N supplies that proof. Sites is the cyclic site predicate of NearestNeighborFreezingUniqueMinimum.

**Theorem 1.2 (The last site diverges).**

$$\forall B \in \mathbb{R},\; \exists N0 \in \mathbb{N},\; \forall N \in \mathbb{N},\; (N0 \leq N \Rightarrow \forall xi \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; (3 \leq N \Rightarrow \operatorname{StrictMono}\left(xi\right) \Rightarrow \operatorname{Sites}\left(xi\right) \Rightarrow B < xi\left(\langle N - 1 \rangle\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection and negation preserve the cyclic equations and the increasing chamber. A maximum-coordinate comparison gives uniqueness, hence the first and last coordinates are −R and R with R > 0. Summing the first k equations retains the wrap-around reciprocal and gives 1/k < R(ξk − ξ(k−1)) in zero-based indices, for 1 ≤ k < N. Summing these gap estimates yields H_(N−1) < 2R², where H_m = Σ_(j=1)^m 1/j. Harmonic divergence then gives the displayed conclusion. Increasing solutions exist for every N ≥ 3 by NearestNeighborFreezingUniqueMinimum.result. The sharper inverse-error-function approximation in Eq. (19) is a separate question.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborLastSiteDivergence.result`
- Dependency: [D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum](NearestNeighborFreezingUniqueMinimum.md)
