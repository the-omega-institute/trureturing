# The imprecise separable CHSH optimum

## Abstract

The sharp separable CHSH value for two qubits with imprecisely calibrated binary observables is attained and optimal.

**Definition 1.1 (The two-qubit CHSH witness).**

$$\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (a_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.witness}\left(\rho, a_{1}, a_{2}, b_{1}, b_{2}\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\rho) \cdot ((((\operatorname{Matrix.kronecker}\left(a_{1}, b_{1}\right)) + (\operatorname{Matrix.kronecker}\left(a_{1}, b_{2}\right))) + (\operatorname{Matrix.kronecker}\left(a_{2}, b_{1}\right))) - (\operatorname{Matrix.kronecker}\left(a_{2}, b_{2}\right)))\right)\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.witness` (`✓ std3`).

*Citation.* Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli (2022). *Entanglement detection with imprecise measurements*. DOI: [10.1103/PhysRevLett.128.250501](https://doi.org/10.1103/PhysRevLett.128.250501). URL: <https://arxiv.org/abs/2202.13131v2>.

*Commentary.*

The witness is the real part of the trace of a two-qubit state times the CHSH matrix. The four tensor products use the two local observables on each side, with the fourth term carrying a minus sign.

**Definition 1.2 (Calibrated binary observables).**

$$\forall (\varepsilon: \mathbb{R}), (\forall (a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (a_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (b_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.Admissible}\left(\varepsilon, a_{1}, a_{2}, b_{1}, b_{2}\right) = \left((\operatorname{D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.IsBinaryObservable}\left(a_{1}\right)) \land ((\operatorname{D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.IsBinaryObservable}\left(a_{2}\right)) \land ((\operatorname{D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.IsBinaryObservable}\left(b_{1}\right)) \land ((\operatorname{D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.IsBinaryObservable}\left(b_{2}\right)) \land ((((2: \mathbb{R})) - (((4: \mathbb{R})) \cdot (\varepsilon)) \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((a_{1}) \cdot (\operatorname{D5.S3.Quantum.FiniteDimensional.qubitX})\right)\right)) \land ((((2: \mathbb{R})) - (((4: \mathbb{R})) \cdot (\varepsilon)) \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((a_{2}) \cdot (\operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ})\right)\right)) \land ((((2: \mathbb{R})) - (((4: \mathbb{R})) \cdot (\varepsilon)) \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((b_{1}) \cdot (\operatorname{D5.S3.Quantum.FiniteDimensional.qubitX})\right)\right)) \land (((2: \mathbb{R})) - (((4: \mathbb{R})) \cdot (\varepsilon)) \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((b_{2}) \cdot (\operatorname{D5.S3.Quantum.FiniteDimensional.qubitZ})\right)\right))))))))\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.Admissible` (`✓ std3`).

*Citation.* Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli (2022). *Entanglement detection with imprecise measurements*. DOI: [10.1103/PhysRevLett.128.250501](https://doi.org/10.1103/PhysRevLett.128.250501). URL: <https://arxiv.org/abs/2202.13131v2>.

*Commentary.*

Four qubit observables are admissible when each is binary and their real trace pairings with the target Pauli X or Z matrix are at least 2 minus 4 epsilon, in the order X, Z, X, Z.

**Definition 1.3 (The calibrated separable value).**

$$\forall (\varepsilon: \mathbb{R}), (\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.separableValue}\left(\varepsilon\right) = \operatorname{ite}\left(\varepsilon \le (\frac{(1: \mathbb{R})}{(2: \mathbb{R})}) - (\frac{(1: \mathbb{R})}{((2: \mathbb{R})) \cdot (\operatorname{Real.sqrt}\left((2: \mathbb{R})\right))}), ((((4: \mathbb{R})) \cdot (((1: \mathbb{R})) - (((2: \mathbb{R})) \cdot (\varepsilon)))) \cdot (\operatorname{Real.sqrt}\left((\varepsilon) \cdot (((1: \mathbb{R})) - (\varepsilon))\right))) + (\operatorname{Real.sqrt}\left(((2: \mathbb{R})) - (((((16: \mathbb{R})) \cdot (\varepsilon)) \cdot (((1: \mathbb{R})) - (\varepsilon))) \cdot (\left(((1: \mathbb{R})) - (((2: \mathbb{R})) \cdot (\varepsilon))\right)^{2}))\right)), (2: \mathbb{R})\right))$$

*Formalization.* `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.separableValue` (`✓ std3`).

*Citation.* Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli (2022). *Entanglement detection with imprecise measurements*. DOI: [10.1103/PhysRevLett.128.250501](https://doi.org/10.1103/PhysRevLett.128.250501). URL: <https://arxiv.org/abs/2202.13131v2>.

*Commentary.*

The value follows the source's two branches. Below the threshold one half minus one over twice the square root of two, it is the explicit expression with a linear calibration term and a square-root term; above the threshold it is the constant two.

**Definition 1.4 (The greatest admissible separable witness value).**

$$(\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.claim}) \Leftrightarrow (\forall (\varepsilon: \mathbb{R}), ((\varepsilon \in \operatorname{Set.Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow (\operatorname{IsGreatest}\left(\{(w: \mathbb{R}) | \exists (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\exists (a_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (a_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\exists (b_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.Separable}\left(\rho\right)) \land ((\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.Admissible}\left(\varepsilon, a_{1}, a_{2}, b_{1}, b_{2}\right)) \land (w = \operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.witness}\left(\rho, a_{1}, a_{2}, b_{1}, b_{2}\right))))))))\}, \operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.separableValue}\left(\varepsilon\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli (2022). *Entanglement detection with imprecise measurements*. DOI: [10.1103/PhysRevLett.128.250501](https://doi.org/10.1103/PhysRevLett.128.250501). URL: <https://arxiv.org/abs/2202.13131v2>.

*Commentary.*

For every epsilon in the unit interval, the displayed separable value is the greatest real number attained by a separable two-qubit state and four admissible binary observables.

**Theorem 1.5 (The separable CHSH optimum is attained and optimal).**

$$\operatorname{D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/morelli-yamasaki-huber-tavakoli-2022-imprecise-chsh-optimum` (proved) by `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"morelli-yamasaki-huber-tavakoli-2022-imprecise-chsh-optimum","declaration_gid":"D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli (2022). *Entanglement detection with imprecise measurements*. DOI: [10.1103/PhysRevLett.128.250501](https://doi.org/10.1103/PhysRevLett.128.250501). URL: <https://arxiv.org/abs/2202.13131v2>.

*Commentary.*

For the upper bound, first compute the witness on a tensor product of two Hermitian trace-one positive semidefinite matrices as the CHSH combination of the four local real expectations. A binary observable on a trace-one positive matrix has expectation in the interval from minus one to one, and the scalar CHSH inequality therefore gives the constant bound two.

In the small-epsilon branch set c equal to 1 minus 2 epsilon and s equal to twice the square root of epsilon times 1 minus epsilon. Their squares sum to one, and the calibration constraints, together with the Bloch decomposition of each observable, give two unit-circle coordinates whose four expectation magnitudes are bounded by the corresponding ellipse. The rectangle reduction and the ellipse CHSH inequality bound the product witness by 2 c s plus the square root of 1 plus (c squared minus s squared) squared. Algebra identifies this with the first branch of separableValue.

Every separable state lies in the convex hull of tensor products. The witness is affine in the state, so the tensor-product bound extends to all separable states.

For attainment in the small branch, take observables in the XZ plane with vectors (c,0,s) and (s,0,c), and use the explicitly constructed positive trace-one qubit state on both factors. Its top singular direction gives the value 2 c s plus the same square root, while the calibration equalities hold. In the large-epsilon branch the scalar CHSH bound is two; four observables with vector (1 over square root of two, 0, 1 over square root of two) and their corresponding product state attain two. The two cases establish both greatestness and attainment for every epsilon.

## References

- Truth anchor: `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.Admissible`
- Truth anchor: `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.claim`
- Truth anchor: `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.result`
- Truth anchor: `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.separableValue`
- Truth anchor: `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.witness`
- Dependency: [D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness](../Quantum/Entanglement/Witness/WernerTesterIncompleteness.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](../Quantum/Measurement/FourQubitParentConstruction.md)
