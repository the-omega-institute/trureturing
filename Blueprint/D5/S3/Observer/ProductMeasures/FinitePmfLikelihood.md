# Finite PMF Likelihood Construction

## Abstract

Finite-coordinate likelihoods construct an absolutely continuous product law.

**Definition 1.1 (Real mass of a finite PMF).**

$$\operatorname{pmfRealMass}\left(p, o\right) = \operatorname{toReal}\left(\operatorname{mass}\left(p, o\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.pmfRealMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite PMF masses are converted from extended nonnegative reals to reals.

**Definition 1.2 (Square-root likelihood ratio).**

$$\operatorname{rootLikelihood}\left(p, q, o\right) = \operatorname{sqrtRatio}\left(\operatorname{pmfRealMass}\left(p, o\right), \operatorname{pmfRealMass}\left(q, o\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.rootLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio is totalized at zero denominators by real division.

**Definition 1.3 (Finite PMF affinity).**

$$\operatorname{affinity}\left(p, q\right) = \operatorname{finiteBhattacharyyaSum}\left(p, q\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.affinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bhattacharyya affinity sums products of square roots of masses.

**Definition 1.4 (Finite PMF Hellinger energy).**

$$\operatorname{energy}\left(p, q\right) = \operatorname{hellingerSquared}\left(p, q\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository convention is H squared equals twice one minus affinity.

**Definition 1.5 (Finite-prefix root likelihood).**

$$\operatorname{prefixRootLikelihood}\left(p, q, n, x\right) = \operatorname{productBefore}\left(n, \operatorname{rootLikelihoodAt}\left(x\right)\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.prefixRootLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first n coordinate likelihood ratios are multiplied.

**Definition 1.6 (Finite tail affinity).**

$$\operatorname{tailAffinity}\left(p, q, m, n\right) = \operatorname{productOnHalfOpenInterval}\left(m, n, affinity\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.tailAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate affinities are multiplied on the half-open interval.

**Definition 1.7 (Countable product law).**

$$\operatorname{productLaw}\left(p\right) = \operatorname{infiniteProductMeasure}\left(p\right)$$

*Formalization.* `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.productLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The infinite product measure is built from the coordinate PMF measures.

**Lemma 1.8 (Real PMF masses are nonnegative).**

$$0 \le \operatorname{pmfRealMass}\left(p, o\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.pmfRealMass_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conversion from extended nonnegative reals preserves nonnegativity.

**Lemma 1.9 (Equivalent local laws share zero atoms).**

$$\operatorname{pmfRealMass}\left(p, o\right) = 0 \Leftrightarrow \operatorname{pmfRealMass}\left(q, o\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.mass_zero_iff_of_ac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mutual absolute continuity transfers null singleton events both ways.

**Lemma 1.10 (Energy is twice one minus affinity).**

$$\operatorname{energy}\left(p, q\right) = 2 \cdot \left(1 - \operatorname{affinity}\left(p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.energy_eq_two_mul_one_sub_affinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization of both finite PMFs yields the standard identity.

**Lemma 1.11 (Affinity is nonnegative).**

$$0 \le \operatorname{affinity}\left(p, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.affinity_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand is a product of nonnegative square roots.

**Lemma 1.12 (Prefix likelihoods belong to L2).**

$$\operatorname{MemLp}\left(\operatorname{prefixRootLikelihood}\left(p, q, n\right), 2, \operatorname{productLaw}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.prefixRootLikelihood_memLp_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite-coordinate function on a probability space is bounded.

**Lemma 1.13 (Prefix expectation factors into affinities).**

$$\operatorname{integral}\left(\operatorname{prefixRootLikelihood}\left(p, q, n\right), \operatorname{productLaw}\left(q\right)\right) = \operatorname{productBefore}\left(n, affinity\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.integral_prefixRootLikelihood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independence of product coordinates factors the finite expectation.

**Theorem 1.14 (Summable energy gives product absolute continuity).**

$$\operatorname{summable}\left(\operatorname{energySequence}\left(p, q\right)\right) \Rightarrow \operatorname{AbsolutelyContinuous}\left(\operatorname{productLaw}\left(p\right), \operatorname{productLaw}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.productLaw_ac_of_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L2 likelihood limits provide a density for the first product law.

## References

- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.affinity`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.affinity_nonneg`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.energy`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.energy_eq_two_mul_one_sub_affinity`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.integral_prefixRootLikelihood`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.mass_zero_iff_of_ac`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.pmfRealMass`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.pmfRealMass_nonneg`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.prefixRootLikelihood`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.prefixRootLikelihood_memLp_two`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.productLaw`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.productLaw_ac_of_summable`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.rootLikelihood`
- Truth anchor: `D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.tailAffinity`
- Dependency: [D5/S3/TotalVariation/Hellinger](../../TotalVariation/Hellinger.md)
