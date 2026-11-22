# Classical value of the complete-graph coloring game

## Abstract

The weighted complete-graph coloring game has a sharp classical value from two attainable deterministic scores.

Alice and Bob each receive a vertex and answer with a color. The inputs are ordered. They win when equal inputs have equal answers and unequal inputs have unequal answers. Shared and private random choices independent of the input can be sampled as complete local tables before play. Their distribution ranges over the whole real standard simplex of table pairs.

**Definition 1.1 (Balanced sum of squares).**

$$\forall (k: \mathbb{N}), \forall (s: \mathbb{N}), \operatorname{B}\left(k, s\right) = k \times (s \operatorname{div} k)^{2}+(2 \times (s \operatorname{div} k)+1) \times (s \operatorname{mod} k)$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

For a positive number k of colors, divide s by k in the natural numbers. Assign the quotient plus one to the remainder many colors and the quotient to all other colors. This minimizes the sum of squares. Zero colors permit only an empty block, with B(0,0)=0. The displayed formula uses Lean's total natural division and remainder.

**Definition 1.2 (Size of the common block).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \forall (t: \mathbb{R}), \operatorname{commonSize}\left(n, k, t\right) = \operatorname{min}\left(n, k \times \operatorname{NatCeil}\left(\frac{t}{2}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.commonSize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

NatCeil is the natural ceiling. For the admissible nonnegative t it is the usual real ceiling. The number of common inputs is capped at n.

**Definition 1.3 (Pairs of local response tables).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \operatorname{Strategy}\left(n, m\right) = (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right))$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.Strategy` (`✓ std3`).

*Citation.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

The first table belongs to Alice and the second to Bob. Both range over all functions from vertices to colors.

**Definition 1.4 (Ordered referee weights).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall ((x, y): \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)), \operatorname{inputWeight}\left(n, p, (x, y)\right) = \operatorname{ite}\left(x = y, \frac{p}{(n: \mathbb{R})}, \frac{1-p}{(n: \mathbb{R}) \times ((n: \mathbb{R})-1)}\right)$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.inputWeight` (`✓ std3`).

*Citation.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

For n>1, the diagonal receives total mass p and the off-diagonal receives total mass 1−p across both input orders.

**Definition 1.5 (Deterministic winning probability).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (p: \mathbb{R}), \forall (\rho: \operatorname{Strategy}\left(n, m\right)), \operatorname{detWin}\left(n, m, p, \rho\right) = \sum_{(x, y): \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(x = y \Leftrightarrow \rho.1\left(x\right) = \rho.2\left(y\right), \operatorname{inputWeight}\left(n, p, (x, y)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.detWin` (`✓ std3`).

*Citation.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

Sum the input weight exactly when the input and output equalities have the same truth value.

**Definition 1.6 (Classical winning probability).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (p: \mathbb{R}), \forall (\mu: \operatorname{StdSimplex}\left(\mathbb{R}, \operatorname{Strategy}\left(n, m\right)\right)), \operatorname{mixedWin}\left(n, m, p, \mu\right) = \sum_{\rho: \operatorname{Strategy}\left(n, m\right)} \operatorname{weights}\left(\mu, \rho\right) \times \operatorname{detWin}\left(n, m, p, \rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.mixedWin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

Average deterministic winning probabilities against a single distribution of ordered table pairs, independent of the input.

**Definition 1.7 (Ratio of diagonal to off-diagonal weights).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \operatorname{tParam}\left(n, p\right) = \frac{p \times ((n: \mathbb{R})-1)}{1-p}$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.tParam` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

The ratio is p(n−1)/(1−p) on the low-diagonal interval.

**Definition 1.8 (Conversion from score to probability).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{probability}\left(n, p, s\right) = 1-p+\frac{1-p}{(n: \mathbb{R}) \times ((n: \mathbb{R})-1)} \times s$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.probability` (`✓ std3`).

*Citation.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

The baseline is the total off-diagonal mass. One unit of score contributes one off-diagonal input weight.

**Definition 1.9 (Score of a deterministic table pair).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (t: \mathbb{R}), \forall (\rho: \operatorname{Strategy}\left(n, m\right)), \operatorname{detScore}\left(n, m, t, \rho\right) = (1+t) \times (\operatorname{card}\left(\{x: \operatorname{Fin}\left(n\right) \mid \rho.1\left(x\right) = \rho.2\left(x\right)\}\right): \mathbb{R})-(\operatorname{card}\left(\{(x, y): \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right) \mid \rho.1\left(x\right) = \rho.2\left(y\right)\}\right): \mathbb{R})$$

*Formalization.* `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.detScore` (`✓ std3`).

*Citation.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

Count diagonal agreements with coefficient 1+t and subtract ordered color collisions. For each color i, the collision contribution is the product of its two table counts.

**Theorem 1.10 (Exact low-diagonal classical value).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (p: \mathbb{R}), ((2 \le m \land m < n) \land (0 < p < \frac{2}{(m: \mathbb{R})+2})) \Rightarrow ((\operatorname{IsGreatest}\left(\operatorname{range}\left(\operatorname{mixedWin}\left(n, m, p\right)\right), 1-p+\frac{1-p}{(n: \mathbb{R}) \times ((n: \mathbb{R})-1)} \times \operatorname{max}\left((1+\operatorname{tParam}\left(n, p\right)) \times (n: \mathbb{R})-(\operatorname{B}\left(m, n\right): \mathbb{R}), (1+\operatorname{tParam}\left(n, p\right)) \times (\operatorname{commonSize}\left(n, (m-2), \operatorname{tParam}\left(n, p\right)\right): \mathbb{R})-(\operatorname{B}\left((m-2), \operatorname{commonSize}\left(n, (m-2), \operatorname{tParam}\left(n, p\right)\right)\right): \mathbb{R})\right)\right)) \land \left((\exists (A: \operatorname{Strategy}\left(n, m\right)), \exists (C: \operatorname{Strategy}\left(n, m\right)), ((\operatorname{detScore}\left(n, m, \operatorname{tParam}\left(n, p\right), A\right) = (1+\operatorname{tParam}\left(n, p\right)) \times (n: \mathbb{R})-(\operatorname{B}\left(m, n\right): \mathbb{R})) \land (\operatorname{detScore}\left(n, m, \operatorname{tParam}\left(n, p\right), C\right) = (1+\operatorname{tParam}\left(n, p\right)) \times (\operatorname{commonSize}\left(n, (m-2), \operatorname{tParam}\left(n, p\right)\right): \mathbb{R})-(\operatorname{B}\left((m-2), \operatorname{commonSize}\left(n, (m-2), \operatorname{tParam}\left(n, p\right)\right)\right): \mathbb{R})))) \land (\sum_{(x, y): \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)} \operatorname{inputWeight}\left(n, p, (x, y)\right) = 1)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Bolduc, Michael Jennings (2026). *Quantum Coloring Games on Complete Graphs*. DOI: [10.48550/arXiv.2611.19002](https://doi.org/10.48550/arXiv.2611.19002). URL: <https://arxiv.org/html/2611.19002v1>.

*Commentary.*

The two scores use t=p(n−1)/(1−p), λ=1+t, d=m−2 and s=min(n,d⌈t/2⌉). They are λn−B(m,n) and λs−B(d,s). IsGreatest certifies attainment and a bound on every classical mixture. Two deterministic pairs attain the respective scores, and the last equality normalizes the ordered input weights.

For arbitrary marginals, remove their pointwise minimum. The two residual supports are disjoint. If the residual mass vanishes, the balanced-square minimum bounds the score by the synchronous value. Otherwise choose a color of least common count on each residual support. With common counts a and b and remaining total R, parity gives R a b ≤ (a+b)⌊R/2⌋⌈R/2⌉. The resulting score is bounded by the greater of the two endpoint scores.

For d>0, the difference of successive common-block scores is t−2⌊s/d⌋. Its sign makes the stated capped ceiling a maximizing size, including zero differences at ties. When m=2, the common block is empty and its score is zero.

A balanced synchronous coloring attains the first score. For the second, both players use the same balanced coloring with colors 2 through m−1 on the first s inputs. On the remaining inputs Alice uses color 0 and Bob uses color 1. A point mass on the better pair attains the classical value.

## References

- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.B`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.Strategy`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.commonSize`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.detScore`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.detWin`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.inputWeight`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.mixedWin`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.probability`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.result`
- Truth anchor: `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.tParam`
