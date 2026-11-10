# Optimality of the finite-graph moving-particle constant

## Abstract

Linear occupation observables force every moving-particle constant k to satisfy one at most k times the effective conductance.

**Definition 1.1 (Symmetric nonnegative conductances).**

$$\forall \left(v: \operatorname{Type}\right), \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{IsConductance}\left(c\right)\right) \Leftrightarrow \left(\left(\forall \left(u: v\right), \left(\forall \left(w: v\right), \left(\left(0: \mathbb{R}\right) \le c\left(u, w\right)\right)\right)\right) \land \left(\forall \left(u: v\right), \left(\forall \left(w: v\right), \left(c\left(u, w\right) = c\left(w, u\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.IsConductance` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

A conductance is a nonnegative symmetric real function of two vertices. Zero weights represent absent edges. This expresses the weighted undirected graph of Chen, OctopusMoving_v3.tex, line 111, on a vertex type. The definition also allows disconnected networks and diagonal weights; diagonal pairs contribute zero to both energies.

**Definition 1.2 (Exchanging two occupations).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{DecidableEq}\left(v\right)], \left(\forall \left(x: v\right), \left(\forall \left(y: v\right), \left(\forall \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\left(\operatorname{swap}\left(x, y, \zeta\right): \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) = \operatorname{Function.comp}\left(\zeta, \operatorname{Equiv.toFun}\left(\operatorname{Equiv.swap}\left(x, y\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.swap` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

A configuration assigns an element of Fin 2 to each vertex, with zero empty and one occupied. Precomposition with the transposition of x and y exchanges their occupations. When x equals y it fixes the configuration. This is the exchange defined in Chen, OctopusMoving_v3.tex, lines 116–120.

**Definition 1.3 (The swap gradient).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{DecidableEq}\left(v\right)], \left(\forall \left(x: v\right), \left(\forall \left(y: v\right), \left(\forall \left(f: \left(\left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\left(\operatorname{grad}\left(x, y, f, \zeta\right): \mathbb{R}\right) = \left(f\left(\operatorname{swap}\left(x, y, \zeta\right)\right)\right) - \left(f\left(\zeta\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.grad` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

The gradient is the change in a real observable f after exchanging x and y. Its sign is the value after the exchange minus the original value, as in Chen, OctopusMoving_v3.tex, line 116.

**Definition 1.4 (Product Bernoulli mass).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left(\forall \left(\alpha: \mathbb{R}\right), \left(\forall \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right), \left(\left(\operatorname{bernoulli}\left(\alpha, \zeta\right): \mathbb{R}\right) = \prod_{z: v} \left(\operatorname{ite}\left(\zeta\left(z\right) = \left(1: \operatorname{Fin}\left(2\right)\right), \alpha, \left(\left(1: \mathbb{R}\right)\right) - \left(\alpha\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.bernoulli` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

Multiply one factor for each vertex: α at an occupied vertex and 1 − α at an empty vertex. For α between zero and one this is the constant-density product Bernoulli probability mass of Chen, OctopusMoving_v3.tex, lines 122–123. The expression is defined for every real α.

**Definition 1.5 (Expectation of an observable).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left(\forall \left(\alpha: \mathbb{R}\right), \left(\forall \left(f: \left(\left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{expect}\left(\alpha, f\right): \mathbb{R}\right) = \operatorname{dotProduct}\left(\operatorname{bernoulli}\left(\alpha\right), f\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.expect` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

The dot product sums the value of f at each configuration multiplied by its Bernoulli mass. This is the finite-space version of the expectation notation introduced in Chen, OctopusMoving_v3.tex, line 128. For real α outside the probability interval the same finite weighted sum remains defined.

**Definition 1.6 (The exclusion Dirichlet energy).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left([\operatorname{DecidableEq}\left(v\right)], \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(\alpha: \mathbb{R}\right), \left(\forall \left(f: \left(\left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{exclusionEnergy}\left(c, \alpha, f\right): \mathbb{R}\right) = \left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \cdot \left(\left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \cdot \left(\sum_{u: v} \left(\sum_{w: v} \left(\left(c\left(u, w\right)\right) \cdot \left(\operatorname{expect}\left(\alpha, \lambda \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(\operatorname{grad}\left(u, w, f, \zeta\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.exclusionEnergy` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

Sum each squared swap gradient in expectation, weighted by its conductance. The inner factor one half converts the sum over ordered vertex pairs into a sum over undirected edges. The outer factor one half is the Dirichlet-energy prefactor in Chen, OctopusMoving_v3.tex, lines 125–126.

**Definition 1.7 (The electrical Dirichlet energy).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(h: \left(v\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{electricEnergy}\left(c, h\right): \mathbb{R}\right) = \left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \cdot \left(\sum_{u: v} \left(\sum_{w: v} \left(\left(c\left(u, w\right)\right) \cdot \left(\left(\left(h\left(u\right)\right) - \left(h\left(w\right)\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.electricEnergy` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

For a real potential h, sum each squared potential difference weighted by its conductance. The factor one half removes the duplication of each undirected edge in the ordered-pair sum. This is the electrical energy in Chen, OctopusMoving_v3.tex, lines 160–165.

**Definition 1.8 (The unit-voltage infimum).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\forall \left(x: v\right), \left(\forall \left(y: v\right), \left(\left(\operatorname{effectiveConductance}\left(c, x, y\right): \mathbb{R}\right) = \operatorname{sInf}\left(\{\left(e: \mathbb{R}\right) \mid \exists \left(h: \left(v\right) \to \left(\mathbb{R}\right)\right), \left(\left(h\left(x\right) = \left(1: \mathbb{R}\right)\right) \land \left(\left(h\left(y\right) = \left(0: \mathbb{R}\right)\right) \land \left(e = \operatorname{electricEnergy}\left(c, h\right)\right)\right)\right)\}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.effectiveConductance` (`✓ std3`).

*Citation.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

Take the real infimum of electrical energies of potentials equal to one at x and zero at y. For distinct vertices and nonnegative conductances, this set is nonempty and bounded below by zero. It is the reciprocal-effective-resistance expression in Chen, OctopusMoving_v3.tex, line 141. The definition uses the real sInf operation for all arguments, including those for which the unit-voltage conditions are inconsistent.

**Definition 1.9 (The converse inequality at every nondegenerate density).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left([\operatorname{DecidableEq}\left(v\right)], \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{IsConductance}\left(c\right)\right) \to \left(\forall \left(x: v\right), \left(\forall \left(y: v\right), \left(\left(x \ne y\right) \to \left(\forall \left(\alpha: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \alpha\right) \to \left(\left(\alpha < \left(1: \mathbb{R}\right)\right) \to \left(\forall \left(k: \mathbb{R}\right), \left(\left(\forall \left(f: \left(\left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \cdot \left(\operatorname{expect}\left(\alpha, \lambda \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(\operatorname{grad}\left(x, y, f, \zeta\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right) \le \left(k\right) \cdot \left(\operatorname{exclusionEnergy}\left(c, \alpha, f\right)\right)\right)\right) \to \left(\left(1: \mathbb{R}\right) \le \left(k\right) \cdot \left(\operatorname{effectiveConductance}\left(c, x, y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

Chen, OctopusMoving_v3.tex, lines 177–179, conjectures optimality on finite weighted graphs and on resistance spaces. Here the finite-graph converse says that if a real constant k bounds the exchange cost by k times the exclusion energy for every real observable, then k times the effective conductance is at least one. The quantifiers include every finite vertex type, every nonnegative symmetric conductance, every pair of distinct vertices and every density strictly between zero and one. For the source's graphs with positive effective conductance, combining this converse with the published upper bound, Theorem 1, lines 131–145, gives the least constant. At zero effective conductance there is no admissible finite real constant. The densities zero and one are excluded: their probability masses are supported on constant configurations, where every swap gradient vanishes.

**Theorem 1.10 (Every admissible constant dominates the resistance).**

$$\forall \left(v: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(v\right)], \left([\operatorname{DecidableEq}\left(v\right)], \left(\forall \left(c: \left(v\right) \to \left(\left(v\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{IsConductance}\left(c\right)\right) \to \left(\forall \left(x: v\right), \left(\forall \left(y: v\right), \left(\left(x \ne y\right) \to \left(\forall \left(\alpha: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \alpha\right) \to \left(\left(\alpha < \left(1: \mathbb{R}\right)\right) \to \left(\forall \left(k: \mathbb{R}\right), \left(\left(\forall \left(f: \left(\left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \cdot \left(\operatorname{expect}\left(\alpha, \lambda \left(\zeta: \left(v\right) \to \left(\operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(\operatorname{grad}\left(x, y, f, \zeta\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right) \le \left(k\right) \cdot \left(\operatorname{exclusionEnergy}\left(c, \alpha, f\right)\right)\right)\right) \to \left(\left(1: \mathbb{R}\right) \le \left(k\right) \cdot \left(\operatorname{effectiveConductance}\left(c, x, y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-2017-exclusion-moving-particle-optimality` (proved) by `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-2017-exclusion-moving-particle-optimality","declaration_gid":"D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joe P. Chen (2017). *The moving particle lemma for the exclusion process on a weighted graph*. DOI: [10.1214/17-ECP82](https://doi.org/10.1214/17-ECP82). URL: <https://arxiv.org/abs/1606.01577v4>.

*Commentary.*

For a real potential h, use the linear occupation observable Fₕ: at ζ its value is the sum over z of h(z) times the natural value of ζ(z), cast to ℝ. For distinct u and w, only these two summands change under the swap. Subtracting gives (h(u) − h(w)) times the difference between the real casts of the occupations at w and u.

First compute expectations of products of single-coordinate functions g: the product mass lets the configuration sum factor into the product over z of (1 − α)g(z,0) + αg(z,1). Choosing one coordinate gives expected occupation α; choosing distinct coordinates u and w gives expected product α². Each real occupation has square equal to itself. Expanding the squared occupation difference therefore gives expectation 2α(1 − α).

Expectation sends the zero function to zero and commutes with multiplication by a real constant. For u equal to w the swap gradient and the potential difference both vanish. For distinct u and w, square the gradient formula and pull out the squared potential difference. Thus for all u and w the expected squared gradient of Fₕ is 2α(1 − α)(h(u) − h(w))². Substitution into the ordered-pair sum gives exclusionEnergy(c,α,Fₕ) = α(1 − α) electricEnergy(c,h). If h(x) = 1 and h(y) = 0, half the expected squared x,y-gradient is α(1 − α).

Nonnegative conductances make every electrical energy nonnegative. For distinct x and y the potential equal to one at x and zero elsewhere satisfies the unit-voltage conditions, so the feasible energy set is nonempty. Suppose 1 ≤ k electricEnergy(c,h) for every feasible h. Testing any such potential shows k > 0: otherwise its nonnegative energy would make the right side nonpositive. Division by k shows that 1/k bounds every feasible energy from below. The defining infimum is consequently at least 1/k, and multiplication by k gives 1 ≤ k effectiveConductance(c,x,y).

Finally fix the finite conductance network, distinct x and y, density 0 < α < 1 and an admissible k. For each unit-voltage potential h, apply the assumed moving-particle bound to Fₕ. The two identities give α(1 − α) ≤ k α(1 − α) electricEnergy(c,h). Since α(1 − α) is positive, cancellation yields 1 ≤ k electricEnergy(c,h) for every feasible h. The infimum argument proves the conclusion.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.IsConductance`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.bernoulli`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.effectiveConductance`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.electricEnergy`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.exclusionEnergy`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.expect`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.grad`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.swap`
