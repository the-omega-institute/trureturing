# The minimum distance for rebit exclusion strategies

## Abstract

The minimum average trace distance from the four-input exclusion distribution over all rebit strategies is exactly one twelfth.

**Definition 1.1 (The exclusion distribution).**

$$\forall x \in \operatorname{Fin}\left(4\right),\; \forall y \in \operatorname{Fin}\left(4\right),\; \operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.target}\left(x, y\right) = (\text{if} x = y \text{then} 0 \text{else} \frac{1}{3})$$

*Formalization.* `D5/S3/QuantumBounds/RebitExclusionDistance.target` (`✓ std3`).

*Citation.* Thomas J. Elliott (2025). *Strict advantage of complex quantum theory in a communication task*. DOI: [10.1103/PhysRevA.111.062401](https://doi.org/10.1103/PhysRevA.111.062401). URL: <https://arxiv.org/abs/2505.16523v2>.

*Commentary.*

Section III.A uses four inputs and four outputs. The target probability is zero when the output equals the input and one third otherwise.

**Definition 1.2 (Real states and a real measurement).**

$$\forall rho \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; \forall E \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; (\operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.IsRebitStrategy}\left(rho, E\right)) \Leftrightarrow ((\forall x \in \operatorname{Fin}\left(4\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\left(x\right)\right)) \land (\operatorname{Matrix.trace}\left(rho\left(x\right)\right) = 1)) \land ((\forall y \in \operatorname{Fin}\left(4\right),\; \operatorname{Matrix.PosSemidef}\left(E\left(y\right)\right)) \land (\sum_{y: \operatorname{Fin}\left(4\right)} (E\left(y\right)) = 1)))$$

*Formalization.* `D5/S3/QuantumBounds/RebitExclusionDistance.IsRebitStrategy` (`✓ std3`).

*Citation.* Thomas J. Elliott (2025). *Strict advantage of complex quantum theory in a communication task*. DOI: [10.1103/PhysRevA.111.062401](https://doi.org/10.1103/PhysRevA.111.062401). URL: <https://arxiv.org/abs/2505.16523v2>.

*Commentary.*

A strategy consists of four real positive-semidefinite two by two states of trace one and four real positive-semidefinite measurement effects whose sum is the identity matrix. Over the real numbers, Matrix.PosSemidef includes symmetry. Mixed states cover Alice's private randomness, and positive-operator-valued measurements cover Bob's private randomness and post-processing, including the dilated measurement in Appendix D. The players have no shared randomness or correlations between rounds.

**Definition 1.3 (The average trace distance).**

$$\forall rho \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; \forall E \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; \operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.dist}\left(rho, E\right) = \frac{1}{4} \cdot \sum_{x: \operatorname{Fin}\left(4\right)} (\frac{1}{2} \cdot \sum_{y: \operatorname{Fin}\left(4\right)} (\left|\operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.target}\left(x, y\right) - \operatorname{Matrix.trace}\left(rho\left(x\right) \cdot E\left(y\right)\right)\right|))$$

*Formalization.* `D5/S3/QuantumBounds/RebitExclusionDistance.dist` (`✓ std3`).

*Citation.* Thomas J. Elliott (2025). *Strict advantage of complex quantum theory in a communication task*. DOI: [10.1103/PhysRevA.111.062401](https://doi.org/10.1103/PhysRevA.111.062401). URL: <https://arxiv.org/abs/2505.16523v2>.

*Commentary.*

Section IV and Appendix D measure the error by averaging the trace distance between the target and realized output distributions over the four equally weighted inputs. For input x and output y, the realized probability is Matrix.trace of the product of the state and the effect. The factor one half gives the trace distance of the two distributions for each input.

**Definition 1.4 (One twelfth is the attained minimum).**

$$(\operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.claim}) \Leftrightarrow (\operatorname{IsLeast}\left(\{d: \mathbb{R} \mid \exists rho \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; \exists E \in (\operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)),\; (\operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.IsRebitStrategy}\left(rho, E\right)) \land (d = \operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.dist}\left(rho, E\right)) \}, \frac{1}{12}\right))$$

*Formalization.* `D5/S3/QuantumBounds/RebitExclusionDistance.claim` (`✓ std3`).

*Citation.* Thomas J. Elliott (2025). *Strict advantage of complex quantum theory in a communication task*. DOI: [10.1103/PhysRevA.111.062401](https://doi.org/10.1103/PhysRevA.111.062401). URL: <https://arxiv.org/abs/2505.16523v2>.

*Commentary.*

Appendix D constructs a rebit strategy with average trace distance one twelfth and conjectures that this is the minimum. IsLeast states both that one twelfth belongs to the set of attained distances and that it is at most every element of that set. The set includes mixed states and every four-outcome real positive-operator-valued measurement.

**Theorem 1.5 (The minimum is exactly one twelfth).**

$$\operatorname{D5.S3.QuantumBounds.RebitExclusionDistance.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/RebitExclusionDistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/elliott-2025-rebit-minimum-distance` (proved) by `D5/S3/QuantumBounds/RebitExclusionDistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"elliott-2025-rebit-minimum-distance","declaration_gid":"D5/S3/QuantumBounds/RebitExclusionDistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Thomas J. Elliott (2025). *Strict advantage of complex quantum theory in a communication task*. DOI: [10.1103/PhysRevA.111.062401](https://doi.org/10.1103/PhysRevA.111.062401). URL: <https://arxiv.org/abs/2505.16523v2>.

*Commentary.*

The four real symmetric two by two states lie in a three-dimensional real vector space, so they are linearly dependent. Taking the trace of a nonzero linear relation shows that its coefficients sum to zero. Applying the trace against any effect makes the same relation vanish for the realized probabilities, whereas its value for the target probabilities is minus the corresponding coefficient divided by three.

The triangle inequality bounds the absolute value of each coefficient divided by three by the largest absolute coefficient times the total error in the corresponding output column. A nonzero coefficient family with sum zero has L1 norm at least twice its largest absolute coefficient. Summing the column estimates therefore gives total absolute error at least two thirds, and the factors one fourth and one half give average trace distance at least one twelfth.

An explicit strategy with square root of three attains the bound. Its first three input rows equal the target rows, while its fourth row repeats the third. The total absolute error is two thirds, so the average trace distance is one twelfth. This realizes the construction in Appendix D as a real positive-operator-valued measurement and proves the conjectured minimum.

## References

- Truth anchor: `D5/S3/QuantumBounds/RebitExclusionDistance.IsRebitStrategy`
- Truth anchor: `D5/S3/QuantumBounds/RebitExclusionDistance.claim`
- Truth anchor: `D5/S3/QuantumBounds/RebitExclusionDistance.dist`
- Truth anchor: `D5/S3/QuantumBounds/RebitExclusionDistance.result`
- Truth anchor: `D5/S3/QuantumBounds/RebitExclusionDistance.target`
