# Krawec recycled-coin nonuniformity

## Abstract

A noninteger memory parameter gives a nonuniform recycled-coin return average.

**Definition 1.1 (Conditional coin angle).**

$$\forall phi \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.angle}\left(phi, i\right) = \operatorname{ite}\left(i = (0: \operatorname{Fin}\left(2\right)), \frac{\operatorname{Real.pi}}{4}, \frac{\operatorname{Real.pi} \cdot (1 + phi)}{4}\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.angle` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Equation (4) assigns angle π/4 when the inactive coin is zero and π(1+φ)/4 when it is one. The definition accepts every real memory parameter.

**Definition 1.2 (Conditional coin flip).**

$$\forall d \in \mathbb{N},\; \forall phi \in \mathbb{R},\; \forall psi \in (\operatorname{ZMod}\left(d\right) \to ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C})),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall c \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.coinFlip}\left(phi, psi, n, c\right) = \sum_{(b: \operatorname{Fin}\left(2\right))} (\operatorname{Complex.ofReal}\left(\operatorname{D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3}\left(\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.angle}\left(phi, \operatorname{Prod.fst}\left(c\right)\right), \operatorname{Prod.snd}\left(c\right), b\right)\right) \cdot psi\left(n, (\operatorname{Prod.fst}\left(c\right), b)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.coinFlip` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Equations (3) and (4) apply the real matrix with rows (cos θ, sin θ) and (sin θ, −cos θ) to the active coin. FreeSpectrahedronFeasibilityWitness.X3 is that real matrix; Complex.ofReal casts each entry to a complex scalar before multiplication by an amplitude. Positions belong to ZMod d and coin indices to Fin 2 × Fin 2.

**Definition 1.3 (Conditional cyclic shift).**

$$\forall d \in \mathbb{N},\; \forall psi \in (\operatorname{ZMod}\left(d\right) \to ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C})),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall c \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.shift}\left(psi, n, c\right) = psi\left(n + \operatorname{ite}\left(\operatorname{Prod.snd}\left(c\right) = (0: \operatorname{Fin}\left(2\right)), (1: \operatorname{ZMod}\left(d\right)), -(1: \operatorname{ZMod}\left(d\right))\right), c\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.shift` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

The shift following Equation (4) moves basis positions by minus one for active coin zero and plus one for active coin one. On amplitudes, the value at n therefore comes from n+1 or n−1, respectively. Addition and both displacement values are in ZMod d.

**Definition 1.4 (Exchange of the coins).**

$$\forall d \in \mathbb{N},\; \forall psi \in (\operatorname{ZMod}\left(d\right) \to ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C})),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall c \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.swap}\left(psi, n, c\right) = psi\left(n, (\operatorname{Prod.snd}\left(c\right), \operatorname{Prod.fst}\left(c\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.swap` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Equation (5) exchanges the inactive and active coin indices and preserves the position.

**Definition 1.5 (One step of the walk).**

$$\forall d \in \mathbb{N},\; \forall phi \in \mathbb{R},\; \forall psi \in (\operatorname{ZMod}\left(d\right) \to ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C})),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.U}\left(phi, psi\right) = \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.swap}\left(\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.shift}\left(\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.coinFlip}\left(phi, psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.U` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Equation (6) first flips the active coin, then shifts the position, and finally exchanges the coins.

**Definition 1.6 (State localized at zero).**

$$\forall d \in \mathbb{N},\; \forall alpha \in ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall c \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.initial}\left(alpha, n, c\right) = \operatorname{ite}\left(n = (0: \operatorname{ZMod}\left(d\right)), alpha\left(c\right), (0: \mathbb{C})\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.initial` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

The initial states in §III.B place an arbitrary coin amplitude at position zero. Every other position has zero amplitude; normalization is expressed separately by unitCoin.

**Definition 1.7 (Position probability after iteration).**

$$\forall d \in \mathbb{N},\; \forall phi \in \mathbb{R},\; \forall alpha \in ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall t \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.p}\left(phi, alpha, n, t\right) = \sum_{(c: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))} (\operatorname{Complex.normSq}\left(\left((\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.U}\left(phi\right))^{[t]}\right)\left((\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.initial}\left(alpha\right): (\operatorname{ZMod}\left(d\right) \to ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}))), n, c\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.p` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Equation (7) sums the squared complex amplitudes over all four coin indices after t steps. The notation f^[t] means Nat.iterate f t, including the identity at t=0. The initial state is localized at position zero.

**Definition 1.8 (Finite Cesàro average).**

$$\forall d \in \mathbb{N},\; \forall phi \in \mathbb{R},\; \forall alpha \in ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}),\; \forall n \in \operatorname{ZMod}\left(d\right),\; \forall T \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.avg}\left(phi, alpha, n, T\right) = \frac{\sum_{t \in \operatorname{Finset.range}\left(T\right)} (\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.p}\left(phi, alpha, n, t + 1\right))}{(\operatorname{Nat.cast}\left(T\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.avg` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

The finite average in Equation (8) sums probabilities at times 1 through T. Finset.range T indexes this sum by t=0 through T−1, with the probability evaluated at t+1. The denominator is the real cast of T; at T=0 the empty sum and real division give zero.

**Definition 1.9 (The conjectured exceptional parameters).**

$$\forall d \in \mathbb{N},\; \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.exceptional}\left(d\right) = \operatorname{ite}\left(12 \mid d, (\left\{0, 1, 2, 4, 5, 6\right\}: \operatorname{Set}\left(\mathbb{R}\right)), (\left\{0, 2, 4, 6\right\}: \operatorname{Set}\left(\mathbb{R}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.exceptional` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Sections III.B and IV distinguish two sets of memory parameters: {0,1,2,4,5,6} when twelve divides the cycle size, and {0,2,4,6} otherwise. Each set consists of real numbers.

**Definition 1.10 (Normalized coin state).**

$$\forall alpha \in ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}),\; (\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.unitCoin}\left(alpha\right)) \Leftrightarrow (\sum_{(c: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))} (\operatorname{Complex.normSq}\left(alpha\left(c\right)\right)) = (1: \mathbb{R}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.unitCoin` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

The initial coin states in §III.B are normalized: the sum of squared complex amplitudes over Fin 2 × Fin 2 equals one.

**Definition 1.11 (Krawec's uniformity conjecture).**

$$(\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.claim}) \Leftrightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall phi \in \mathbb{R},\; (phi \in \operatorname{Set.Ico}\left((0: \mathbb{R}), 8\right)) \Rightarrow ((\neg (phi \in \operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.exceptional}\left(d\right))) \Rightarrow (\forall alpha \in ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C}),\; (\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.unitCoin}\left(alpha\right)) \Rightarrow (\forall n \in \operatorname{ZMod}\left(d\right),\; \operatorname{Filter.Tendsto}\left(\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.avg}\left(phi, alpha, n\right), (\operatorname{Filter.atTop}: \operatorname{Filter}\left(\mathbb{N}\right)), \operatorname{nhds}\left(\frac{1}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})}\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim` (`✓ std3`).

*Citation.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

Sections III.B and IV conjecture uniformity outside the stated exceptional parameters. For every cycle size d≥2, every φ in [0,8) outside exceptional d, every normalized coin state initially at position zero, and every position n, the finite Cesàro averages are asserted to converge to 1/d as T tends to infinity. Krawec reports numerical checks for d≤300 and leaves a proof as an open problem.

**Theorem 1.12 (The uniformity conjecture is false).**

$$\neg (\operatorname{D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result` (`✓ std3`). ∎

*Resolves.* `Problems/krawec-2015-recycled-coin-uniformity-refutation` (refuted) by `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krawec-2015-recycled-coin-uniformity-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* W. O. Krawec (2015). *History dependent quantum walk on the cycle with an unbalanced coin*. DOI: [10.1016/j.physa.2015.02.061](https://doi.org/10.1016/j.physa.2015.02.061). URL: <https://arxiv.org/abs/1411.6298v1>.

*Commentary.*

For cycle size 12, take the memory parameter 4·arccos((√2/2)·((√5−1)/2))/π−1. It lies strictly between zero and one, outside the exceptional set. Fourier blocks for momenta zero and two share an eigenvalue whose eigenspaces have nonzero coin overlap. The mean ergodic theorem gives convergent Cesàro averages, and a strict surplus in the sum of the four return averages forces some normalized computational basis coin to have return limit greater than 1/12. This contradicts the uniformity conjecture in Krawec's §IV.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.U`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.angle`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.avg`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.coinFlip`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.exceptional`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.initial`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.p`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.shift`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.swap`
- Truth anchor: `D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.unitCoin`
- Dependency: [D5/S3/Fourier/FinitePoisson](../../Fourier/FinitePoisson.md)
- Dependency: [D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness](../Measurement/FreeSpectrahedronFeasibilityWitness.md)
