# Unique minimum of the nearest-neighbor QES chain potential

## Abstract

The nearest-neighbor QES chain potential has a unique minimum at its site configuration.

**Definition 1.1 (The cyclic site equations).**

$$\forall N \in \mathbb{N},\; \forall xi \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{Sites}\left(xi\right) = \left(\forall i \in \operatorname{Fin}\left(N\right),\; xi\left(i\right) = \frac{1}{xi\left(i\right) - xi\left(\operatorname{symm}\left(\operatorname{finRotate}\left(N\right)\right)\left(i\right)\right)} + \frac{1}{xi\left(i\right) - xi\left(\operatorname{finRotate}\left(N\right)\left(i\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.Sites` (`✓ std3`).

*Citation.* A. Enciso; F. Finkel; A. González-López; M. A. Rodríguez (2007). *A novel quasi-exactly solvable spin chain with nearest-neighbors interactions*. DOI: [10.1016/j.nuclphysb.2007.07.001](https://doi.org/10.1016/j.nuclphysb.2007.07.001). URL: <https://arxiv.org/abs/0704.3046v1>.

*Commentary.*

Sites ξ expresses Eq. (6). The cyclic successor is finRotate(N), and its inverse is the predecessor. StrictMono ξ imposes the increasing chamber separately; Fin N uses zero-based indices.

**Definition 1.2 (The nearest-neighbor potential).**

$$\forall N \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{U}\left(x\right) = \sum_{i\in\operatorname{Fin}\left(N\right)} x\left(i\right)^{2} + \sum_{i\in\operatorname{Fin}\left(N\right)} \frac{2}{(x\left(i\right) - x\left(\operatorname{finRotate}\left(N\right)\left(i\right)\right))^{2}} + \sum_{i\in\operatorname{Fin}\left(N\right)} \frac{2}{(x\left(i\right) - x\left(\operatorname{symm}\left(\operatorname{finRotate}\left(N\right)\right)\left(i\right)\right)) \cdot (x\left(i\right) - x\left(\operatorname{finRotate}\left(N\right)\left(i\right)\right))}$$

*Formalization.* `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.U` (`✓ std3`).

*Citation.* A. Enciso; F. Finkel; A. González-López; M. A. Rodríguez (2007). *A novel quasi-exactly solvable spin chain with nearest-neighbors interactions*. DOI: [10.1016/j.nuclphysb.2007.07.001](https://doi.org/10.1016/j.nuclphysb.2007.07.001). URL: <https://arxiv.org/abs/0704.3046v1>.

*Commentary.*

The potential is Eq. (31), with r² = Σ_i x_i² and the two nearest-neighbor interaction sums.

**Definition 1.3 (The unique-minimum claim).**

$$\forall N \in \mathbb{N},\; (3\leq N \Rightarrow \exists xi \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{StrictMono}\left(xi\right) \land \operatorname{Sites}\left(xi\right) \land (\forall x \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{StrictMono}\left(x\right) \Rightarrow (\operatorname{U}\left(x\right) \geq \operatorname{U}\left(xi\right) \land (\operatorname{U}\left(x\right) = \operatorname{U}\left(xi\right) \Rightarrow x = xi))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.claim` (`✓ std3`).

*Citation.* A. Enciso; F. Finkel; A. González-López; M. A. Rodríguez (2007). *A novel quasi-exactly solvable spin chain with nearest-neighbors interactions*. DOI: [10.1016/j.nuclphysb.2007.07.001](https://doi.org/10.1016/j.nuclphysb.2007.07.001). URL: <https://arxiv.org/abs/0704.3046v1>.

*Commentary.*

The paper states after Eqs. (31)–(32), printed p. 13: "The first one is the requirement that ξ be the unique minimum of the potential U in the domain C. Although our numerical calculations suggest that this is indeed the case, we have not been able to provide a rigorous proof of this fact." The encoding uses StrictMono on Fin N → ℝ and cyclic predecessor and successor indices.

**Theorem 1.4 (The unique-minimum theorem).**

$$\forall N \in \mathbb{N},\; (3\leq N \Rightarrow \exists xi \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{StrictMono}\left(xi\right) \land \operatorname{Sites}\left(xi\right) \land (\forall x \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \operatorname{StrictMono}\left(x\right) \Rightarrow (\operatorname{U}\left(x\right) \geq \operatorname{U}\left(xi\right) \land (\operatorname{U}\left(x\right) = \operatorname{U}\left(xi\right) \Rightarrow x = xi))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N ≥ 3, the site configuration supplied by the theorem is the unique minimizer of U on the strictly increasing chamber.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.Sites`
- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.U`
- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/NearestNeighborFreezingUniqueMinimum.result`
