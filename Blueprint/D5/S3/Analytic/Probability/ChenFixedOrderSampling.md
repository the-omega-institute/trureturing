# Fixed-size samples from two balanced strata

## Abstract

Uniform fixed-size sampling and the stratum inclusion identities for Chen's fixed-order problem.

**Definition 1.1 (Sample size).**

$$\forall m : \mathbb{N}, \operatorname{sampleSize}\left(m\right) : \mathbb{N} = \left(m+1\right)^{2}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increasing square sizes index the sampling designs.

**Definition 1.2 (Size of each stratum).**

$$\forall m : \mathbb{N}, \operatorname{stratumSize}\left(m\right) : \mathbb{N} = \operatorname{sampleSize}\left(m\right)^{3}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.stratumSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both strata have this size, so the sample occupies a vanishing fraction of the population.

**Definition 1.3 (Population labels).**

$$\forall m : \mathbb{N}, \operatorname{Population}\left(m\right) : \operatorname{Type} = \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(\operatorname{stratumSize}\left(m\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Population` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate records the stratum and the second the label within it.

**Definition 1.4 (Subsets of the prescribed size).**

$$\forall m : \mathbb{N}, \operatorname{Sample}\left(m\right) : \operatorname{Type} = \operatorname{Subtype}\left(\left(S : \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right)\right) \mapsto \operatorname{card}\left(S\right) = \operatorname{sampleSize}\left(m\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cardinality condition is carried with the underlying finite subset.

**Definition 1.5 (Values of the two strata).**

$$\forall m : \mathbb{N}, \forall j : \operatorname{Population}\left(m\right), \operatorname{populationValue}\left(m, j\right) : \mathbb{R} = \operatorname{ite}\left(j.1 = 0, 1, -1\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The opposite values make the two equal strata balance.

**Definition 1.6 (Population mean).**

$$\forall m : \mathbb{N}, \operatorname{populationMean}\left(m\right) : \mathbb{R} = \frac{\sum_{j : \operatorname{Population}\left(m\right)} \operatorname{populationValue}\left(m, j\right)}{\left(\operatorname{Fintype.card}\left(\operatorname{Population}\left(m\right)\right) : \mathbb{R}\right)}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every label enters with the same weight.

**Definition 1.7 (Centered and scaled sample mean).**

$$\forall m : \mathbb{N}, \forall S : \operatorname{Sample}\left(m\right), \operatorname{estimator}\left(m, S\right) : \mathbb{R} = \sqrt{\operatorname{sampleSize}\left(m\right) : \mathbb{R}} \cdot \left(\frac{\sum_{j \in S.val} \operatorname{populationValue}\left(m, j\right)}{\left(\operatorname{sampleSize}\left(m\right) : \mathbb{R}\right)} - \operatorname{populationMean}\left(m\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.estimator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centering and scaling are shared by the two designs.

**Definition 1.8 (Sample inclusion event).**

$$\forall m : \mathbb{N}, \forall A : \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \operatorname{inclusion}\left(m, A\right) : \operatorname{Set}\left(\operatorname{Sample}\left(m\right)\right) = \{S \mid A \subseteq S.val\}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prescribed subset may be empty.

**Definition 1.9 (Uniform sampling law).**

$$\begin{aligned}\forall m : \mathbb{N}, \operatorname{uniformSampleMeasure}\left(m\right) : \operatorname{ProbabilityMeasure}\left(\operatorname{Sample}\left(m\right)\right),\\\left(\operatorname{uniformSampleMeasure}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right) = \operatorname{uniformOn}\left(\left(\operatorname{Set.univ} : \operatorname{Set}\left(\operatorname{Sample}\left(m\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.uniformSampleMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each sample of the prescribed size receives the same mass.

**Definition 1.10 (Ordered draws with replacement).**

$$\forall m : \mathbb{N}, \operatorname{Draw}\left(m\right) : \operatorname{Type} = \operatorname{Fin}\left(\operatorname{sampleSize}\left(m\right)\right) \to \operatorname{Population}\left(m\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Draw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position index allows a label to occur more than once.

**Definition 1.11 (Distinctness event of an ordered draw).**

$$\forall m : \mathbb{N}, \operatorname{distinct}\left(m\right) : \operatorname{Set}\left(\operatorname{Draw}\left(m\right)\right) = \{d \mid \operatorname{Function.Injective}\left(d\right)\}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.distinct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conditioning on injectivity gives draws without replacement.

**Definition 1.12 (Erasing order).**

$$\begin{aligned}\forall m : \mathbb{N}, \forall d : \operatorname{Draw}\left(m\right), \operatorname{eraseOrder}\left(m, d\right) : \operatorname{Sample}\left(m\right),\\d \in \operatorname{distinct}\left(m\right) \Rightarrow \operatorname{eraseOrder}\left(m, d\right) = \langle\operatorname{Finset.image}\left(d, \operatorname{Finset.univ}\right), h : \operatorname{card}\left(\operatorname{Finset.image}\left(d, \operatorname{Finset.univ}\right)\right) = \operatorname{sampleSize}\left(m\right)\rangle,\\\neg\left(d \in \operatorname{distinct}\left(m\right)\right) \Rightarrow \operatorname{eraseOrder}\left(m, d\right) = \operatorname{Classical.choice}\left(inferInstance : \operatorname{Nonempty}\left(\operatorname{Sample}\left(m\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Injectivity gives the cardinality proof h. Only values on the distinctness event contribute under the conditioned law.

**Theorem 1.13 (Positive sample size).**

$$\forall m : \mathbb{N}, 0 < \operatorname{sampleSize}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sample size is positive at every stage.

**Theorem 1.14 (Zero population mean).**

$$\forall m : \mathbb{N}, \operatorname{populationMean}\left(m\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two strata have equal size and opposite values, so the population mean is zero.

**Theorem 1.15 (Finite image of a distinct draw).**

$$\forall m : \mathbb{N}, \forall d : \operatorname{Draw}\left(m\right), d \in \operatorname{distinct}\left(m\right) \Rightarrow \operatorname{eraseOrder}\left(m, d\right).val = \operatorname{Finset.image}\left(d, \operatorname{Finset.univ}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each injective ordered draw, its unordered sample is exactly the finite image of the draw.

**Theorem 1.16 (Uniform law on fixed-size subsets).**

$$\forall m : \mathbb{N}, \operatorname{Measure.map}\left(\operatorname{eraseOrder}\left(m\right), \operatorname{ProbabilityTheory.cond}\left(\operatorname{uniformOn}\left(\left(\operatorname{Set.univ} : \operatorname{Set}\left(\operatorname{Draw}\left(m\right)\right)\right)\right), \operatorname{distinct}\left(m\right)\right)\right) = \operatorname{uniformOn}\left(\left(\operatorname{Set.univ} : \operatorname{Set}\left(\operatorname{Sample}\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.map_eraseOrder_cond_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Condition the uniform law of ordered draws on having distinct labels, then erase order. Every subset of the required size has the same number of orderings, giving the uniform subset law.

**Theorem 1.17 (Inclusion polynomial).**

$$\begin{aligned}\forall m : \mathbb{N}, \forall A : \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \exists p : \operatorname{Polynomial}\left(\mathbb{R}\right), \operatorname{natDegree}\left(p\right) \leq \operatorname{card}\left(A\right) \land\\\left(\begin{aligned}\forall f : \mathbb{R} \to \mathbb{R}, \int S \in \operatorname{inclusion}\left(m, A\right), \operatorname{f}\left(\operatorname{estimator}\left(m, S\right)\right) d\operatorname{uniformOn}\left(\left(\operatorname{Set.univ} : \operatorname{Set}\left(\operatorname{Sample}\left(m\right)\right)\right)\right) =\\\quad\int S : \operatorname{Sample}\left(m\right), \operatorname{Polynomial.eval}\left(\operatorname{estimator}\left(m, S\right), p\right) \cdot \operatorname{f}\left(\operatorname{estimator}\left(m, S\right)\right) d\operatorname{uniformOn}\left(\left(\operatorname{Set.univ} : \operatorname{Set}\left(\operatorname{Sample}\left(m\right)\right)\right)\right)\end{aligned}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.exists_inclusionPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On each cell of fixed positive-stratum count, the inclusion fraction is the product of two ratios of binomial coefficients. The two counts are affine in the estimator, giving the degree bound. Summing over the cells gives the restricted integral.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Draw`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Population`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.Sample`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.distinct`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder_val`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.estimator`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.exists_inclusionPolynomial`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.inclusion`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.map_eraseOrder_cond_uniform`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean_eq_zero`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationValue`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize_pos`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.stratumSize`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.uniformSampleMeasure`
