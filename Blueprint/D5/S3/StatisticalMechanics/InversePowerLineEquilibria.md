# Inverse-power line: Equilibria

## Abstract

Inverse-power equilibrium rigidity on the real line.

**Definition 1.1 (claim).**

$$\left(\operatorname{claim}\,\iff\,\forall\,s\,:\,\mathbb{R}\,,\,2\,<\,s\,\to\,\left(\exists\,X\,:\,\operatorname{Set}\,\mathbb{R}\,,\,\operatorname{IsSEquilibrium}\,s\,X\right)\,\land\,\left(\forall\,X\,:\,\operatorname{Set}\,\mathbb{R}\,,\,\operatorname{IsSEquilibrium}\,s\,X\,\iff\,\exists\,\alpha\,:\,\mathbb{R}\,,\,0\,<\,\alpha\,\land\,\left(\exists\,\beta\,:\,\mathbb{R}\,,\,X\,=\,\operatorname{arithmeticProgression}\,\alpha\,\beta\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/InversePowerLineEquilibria.claim` (`✓ std3`).

*Citation.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

Remark 5.3 (p. 8): “We make no claim for s > 2; whether the conclusion of Theorem 1.2 holds there remains open.” The proposition extends the whole classification to every real exponent s > 2, including existence and the converse for every set X. It assumes neither an upper gap bound nor a positive lower gap bound.

**Theorem 1.2 (result).**

$$\forall\,s\,:\,\mathbb{R}\,,\,2\,<\,s\,\to\,\left(\exists\,X\,:\,\operatorname{Set}\,\mathbb{R}\,,\,\operatorname{IsSEquilibrium}\,s\,X\right)\,\land\,\left(\forall\,X\,:\,\operatorname{Set}\,\mathbb{R}\,,\,\operatorname{IsSEquilibrium}\,s\,X\,\iff\,\exists\,\alpha\,:\,\mathbb{R}\,,\,0\,<\,\alpha\,\land\,\left(\exists\,\beta\,:\,\mathbb{R}\,,\,X\,=\,\operatorname{arithmeticProgression}\,\alpha\,\beta\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/InversePowerLineEquilibria.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-ferudun2610s2` (proved) by `D5/S3/StatisticalMechanics/InversePowerLineEquilibria.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-ferudun2610s2","declaration_gid":"D5/S3/StatisticalMechanics/InversePowerLineEquilibria.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alper Ferudun (2026). *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions*. DOI: [10.48550/arXiv.2610.06944](https://doi.org/10.48550/arXiv.2610.06944). URL: <https://arxiv.org/abs/2610.06944v1>.

*Commentary.*

For every real s > 2, an equilibrium exists and its point set is exactly an affine image of the integers with positive scale. Reciprocal consecutive gaps are positive harmonic functions for the transformed conductances. On each proper positive sublevel, interval packing and second-moment estimates produce finitely supported functions of arbitrarily small induced energy. A strict exterior harmonic flux contradicts this energy bound unless the reciprocal gaps are constant. Constant gaps reconstruct the progression, and the absolutely convergent p-series gives the converse.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineEquilibria.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/InversePowerLineEquilibria.result`
- Dependency: [D5/S3/StatisticalMechanics/InversePowerLineBasics](InversePowerLineBasics.md)
- Dependency: [D5/S3/StatisticalMechanics/InversePowerLineConductance](InversePowerLineConductance.md)
- Dependency: [D5/S3/StatisticalMechanics/InversePowerLineNetwork](InversePowerLineNetwork.md)
- Dependency: [D5/S3/StatisticalMechanics/InversePowerLinePowerPacking](InversePowerLinePowerPacking.md)
