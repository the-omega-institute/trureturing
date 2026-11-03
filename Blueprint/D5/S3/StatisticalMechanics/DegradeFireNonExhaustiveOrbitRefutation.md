# A non-exhaustive periodic degrade-and-fire trajectory

## Abstract

A saturated three-cell degrade-and-fire system has a nine-firing periodic trajectory with repeated firing labels.

Cell labels are 0-indexed in Lean: 0, 1 and 2 correspond respectively to the source's labels 1, 2 and 3. Vectors written with ![a,b,c] are functions on Fin 3 in that order. The threshold θ is the source's η. The source locators below refer to DynamicsDFNetworksRevised.tex in arXiv:1809.03228v1.

**Definition 1.1 (The unidirectional coupling matrix).**

$$\forall \left(\varepsilon: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right), \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right), \mathbb{R}\right)\right) = \operatorname{Matrix.circulant}\left(![\left(1: \mathbb{R}\right) - \varepsilon, \varepsilon, \left(0: \mathbb{R}\right)]\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.coupling` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

The circulant with first column (1 − ε, ε, 0) has rows (1 − ε, 0, ε), (ε, 1 − ε, 0) and (0, ε, 1 − ε). This is the matrix of Section 4, lines 239–247. The definition allows every real ε; positivity and the threshold restrictions enter the claim.

**Definition 1.2 (Resetting one coordinate).**

$$\forall \left(x: \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.reset}\left(x, i\right): \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right) = \operatorname{Function.update}\left(x, i, \left(1: \mathbb{R}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.reset` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

Replace coordinate i of x by the real number 1 and leave every other coordinate unchanged. This is the instantaneous firing rule in lines 56–64.

**Definition 1.3 (Successive unique firings).**

$$\forall \left(\varepsilon: \mathbb{R}\right), \left(\forall \left(\theta: \mathbb{R}\right), \left(\forall \left(s: \left(\mathbb{N}\right) \to \left(\left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(lab: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right)\right), \left(\forall \left(\tau: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsRun}\left(\varepsilon, \theta, s, lab, \tau\right): \operatorname{Prop}\right) = \left(\forall \left(k: \mathbb{N}\right), \left(\left(\left(0: \mathbb{R}\right) < \tau\left(k\right)\right) \land \left(\left(\forall \left(t: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) \le t\right) \to \left(\left(t < \tau\left(k\right)\right) \to \left(\forall \left(j: \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right), \left(\theta < \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right), \operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.cut}\left(t, s\left(k\right)\right)\right)\left(j\right)\right)\right)\right)\right)\right) \land \left(\left(\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right), \operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.cut}\left(\tau\left(k\right), s\left(k\right)\right)\right)\left(lab\left(k\right)\right) \le \theta\right) \land \left(\left(\forall \left(j: \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right), \left(\left(j \ne lab\left(k\right)\right) \to \left(\theta < \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right), \operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.cut}\left(\tau\left(k\right), s\left(k\right)\right)\right)\left(j\right)\right)\right)\right) \land \left(\left(\forall \left(t: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) \le t\right) \to \left(\left(t \le \tau\left(k\right)\right) \to \left(\operatorname{Function.Injective}\left(\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.cut}\left(t, s\left(k\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\operatorname{Function.Injective}\left(s\left(k + \left(1: \mathbb{N}\right)\right)\right)\right) \land \left(s\left(k + \left(1: \mathbb{N}\right)\right) = \operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.reset}\left(\operatorname{D5.S3.Geometry.FiniteCoordinateTruncation.cut}\left(\tau\left(k\right), s\left(k\right)\right), lab\left(k\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsRun` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

The functions s, lab and τ give the post-firing configurations, the next firing cell and the elapsed time until that firing. At every natural k the elapsed time is positive. Every repressor is strictly above θ before that time; at the endpoint the selected cell is at or below θ and every other cell is strictly above it. Coordinates are pairwise distinct throughout the closed degrading segment and immediately after resetting. The final equality relates the next configuration to that reset. These conditions express the dynamics of lines 52–64 and the post-firing description and distinctness restriction of lines 249–255. No separate coordinate-range assumption is part of this predicate.

**Definition 1.4 (Periodicity of post-firing configurations).**

$$\forall \left(s: \left(\mathbb{N}\right) \to \left(\left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsPeriodic}\left(s\right): \operatorname{Prop}\right) = \exists \left(p: \mathbb{N}\right), \left(\left(\left(0: \mathbb{N}\right) < p\right) \land \left(\forall \left(k: \mathbb{N}\right), \left(s\left(k + p\right) = s\left(k\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsPeriodic` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

A positive natural number p is a period when s(k + p) = s(k) for every natural k. This is periodicity indexed by firings, as in the return condition of lines 377–390; the definition does not separately assert periodicity of lab or τ.

**Definition 1.5 (Exhaustive firing sequences).**

$$\forall \left(lab: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsExhaustive}\left(lab\right): \operatorname{Prop}\right) = \forall \left(k: \mathbb{N}\right), \left(\operatorname{Function.Bijective}\left(![lab\left(k\right), lab\left(k + \left(1: \mathbb{N}\right)\right), lab\left(k + \left(2: \mathbb{N}\right)\right)]\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsExhaustive` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

Every three consecutive labels must form a bijection from Fin 3 to Fin 3, so each cell occurs exactly once in every such window. This is the length-three permutation condition in line 68, with labels shifted from 1, 2, 3 to 0, 1, 2.

**Definition 1.6 (The proposed exclusion of non-exhaustive periodic trajectories).**

$$\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.claim}: \operatorname{Prop}\right) = \left(\forall \left(\theta: \mathbb{R}\right), \left(\forall \left(\varepsilon: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \theta\right) \to \left(\left(\theta < \left(1: \mathbb{R}\right)\right) \to \left(\left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)} < \varepsilon\right) \to \left(\left(\varepsilon < \left(1: \mathbb{R}\right) - \theta\right) \to \left(\forall \left(s: \left(\mathbb{N}\right) \to \left(\left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(lab: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right)\right), \left(\forall \left(\tau: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right), \left(\theta < \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right), s\left(\left(0: \mathbb{N}\right)\right)\right)\left(j\right)\right)\right) \to \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsRun}\left(\varepsilon, \theta, s, lab, \tau\right)\right) \to \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsPeriodic}\left(s\right)\right) \to \left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsExhaustive}\left(lab\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim` (`✓ std3`).

*Citation.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

For 0 < θ < 1 and 1/2 < ε < 1 − θ, the assertion says that every run whose initial repressors are strictly above θ and whose configurations are periodic has an exhaustive firing sequence. This is the statement in the Concluding Remarks, line 373, that the impossibility should extend to every other periodic trajectory with non-exhaustive firing in the right transition graph. The parameter range and graph are specified in lines 239–257. The run predicate makes uniqueness of each firing and distinctness along each segment explicit. The assertion concerns periodic trajectories, without an attraction or asymptotic rarity conclusion.

**Theorem 1.7 (A nine-firing counterexample).**

$$\neg \left(\forall \left(\theta: \mathbb{R}\right), \left(\forall \left(\varepsilon: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \theta\right) \to \left(\left(\theta < \left(1: \mathbb{R}\right)\right) \to \left(\left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)} < \varepsilon\right) \to \left(\left(\varepsilon < \left(1: \mathbb{R}\right) - \theta\right) \to \left(\forall \left(s: \left(\mathbb{N}\right) \to \left(\left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(lab: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right)\right), \left(\forall \left(\tau: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(\left(3: \mathbb{N}\right)\right)\right), \left(\theta < \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.coupling}\left(\varepsilon\right), s\left(\left(0: \mathbb{N}\right)\right)\right)\left(j\right)\right)\right) \to \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsRun}\left(\varepsilon, \theta, s, lab, \tau\right)\right) \to \left(\left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsPeriodic}\left(s\right)\right) \to \left(\operatorname{D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation.IsExhaustive}\left(lab\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/fernandez-2018-degrade-fire-non-exhaustive-orbit-refutation` (refuted) by `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fernandez-2018-degrade-fire-non-exhaustive-orbit-refutation","declaration_gid":"D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bastien Fernandez (2018). *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators*. DOI: [10.1140/epjst/e2018-800068-8](https://doi.org/10.1140/epjst/e2018-800068-8). URL: <https://arxiv.org/abs/1809.03228v1>.

*Commentary.*

Take θ = 3/20 and ε = 4/5. Define s by repeating the following nine configurations, indexed from zero: (11/32,0,1), (3/16,1,27/32), (0,1,19/32), (0,1,11/32), (1,27/32,3/16), (1,19/32,0), (1,11/32,0), (27/32,3/16,1), (19/32,0,1). Define lab by repeating (1,1,1,0,0,0,2,2,2), and τ by repeating (5/32,1/4,1/4) three times. Each function at k is the corresponding entry at k modulo 9.

For a three-coordinate vector, the three pairwise inequalities imply injectivity. For each of the nine configurations, its assigned time is positive. For each coordinate j and each real t less than that time, substituting the circulant entries and the formula max(s(k)(j) − t, 0) gives a repressor strictly above 3/20. Splitting according to the sign of each truncated coordinate reduces these inequalities to linear inequalities in t. At the endpoint the selected cell has repressor 3/20, while the other two remain strictly above it. For the first three endpoints the repressor triples are (57/80,3/20,27/160), (19/40,3/20,23/32) and (11/40,3/20,107/160); substitution gives the endpoint inequalities for all nine configurations.

The same sign splits show that the three degrading coordinates remain pairwise distinct for every t at most the assigned time, hence in particular on its closed nonnegative interval. Each succeeding configuration also has distinct coordinates. Coordinatewise substitution shows that resetting the selected endpoint coordinate to 1 gives exactly the next listed configuration, with the ninth followed by the first. These facts give all seven conditions in the run predicate for each of the nine positions.

For arbitrary natural k, (k + 1) modulo 9 is the successor of k modulo 9 in Fin 9. Thus the nine segment computations give a run at every k. Initially the repressor triple is (139/160,11/40,1/5), with all three entries above 3/20. Adding 9 to k leaves its remainder unchanged, so s(k + 9) = s(k), and 9 is a positive period.

The first three labels are all 1. If the label sequence were exhaustive, its first three-entry vector would be injective. Its values at the distinct indices 0 and 1 coincide, contradicting that injectivity. Finally, 0 < 3/20 < 1 and 1/2 < 4/5 < 1 − 3/20. Applying the proposed universal assertion to these parameters and to s, lab and τ would therefore make this non-exhaustive sequence exhaustive, which is a contradiction.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsExhaustive`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsPeriodic`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.IsRun`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.coupling`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.reset`
- Truth anchor: `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result`
- Dependency: [D5/S3/Geometry/FiniteCoordinateTruncation](../Geometry/FiniteCoordinateTruncation.md)
