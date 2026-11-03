# FiniteMartingaleCoupling

## Abstract

Finite laws have arbitrary nonnegative weights summing to one, including repeated atoms and zero weights. A transition matrix produces one genuine joint probability measure with both exact marginals and every bounded measurable martingale test. Uniform finite laws in convex order admit such a matrix and coupling. The coupling predicate reuses CostTransport.IsCoupling from the frozen optimal-transport library.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Definition 1.1 (IsCoupling).**

$$\forall  \{\alpha  : \operatorname{Type} \operatorname{u}\} \{\beta  : \operatorname{Type} \operatorname{v}\} [\operatorname{MeasurableSpace} \alpha ] [\operatorname{MeasurableSpace} \beta ] (\mu  : \operatorname{ProbDist} \alpha ) (\nu  : \operatorname{ProbDist} \beta ) (\pi  : \operatorname{ProbDist} (\alpha  \times  \beta )), \operatorname{IsCoupling} \mu  \nu  \pi  \iff  \operatorname{CostTransport}.\operatorname{IsCoupling} \pi .\operatorname{toMeasure} \mu .\operatorname{toMeasure} \nu .\operatorname{toMeasure}$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.IsCoupling` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

An actual joint law is a coupling exactly when its two pushforward measures are the specified marginals. This predicate is the existing general measure coupling predicate specialized to probability laws.

**Lemma 1.2 (fst_probability_marginal).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsCoupling} \mu  \nu  \pi  \to  \pi .\operatorname{map} \operatorname{Prod}.\operatorname{fst} \operatorname{measurablefst} = \mu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.fst_probability_marginal` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The first probability-law pushforward agrees with the first specified marginal.

**Lemma 1.3 (snd_probability_marginal).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsCoupling} \mu  \nu  \pi  \to  \pi .\operatorname{map} \operatorname{Prod}.\operatorname{snd} \operatorname{measurablesnd} = \nu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.snd_probability_marginal` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The second probability-law pushforward agrees with the second specified marginal.

**Lemma 1.4 (supportsOn_Icc_prod).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsCoupling} \mu  \nu  \pi  \to  \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \nu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \operatorname{coe} \pi  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b} \times \operatorname{set}  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.supportsOn_Icc_prod` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A genuine coupling of two laws concentrated on the same closed interval is concentrated on its Cartesian square.

**Definition 1.5 (IsMartingaleCoupling).**

$$\forall  (\mu  \nu  : \operatorname{ProbDist} \mathbb{R} ) (\pi  : \operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )), \operatorname{IsMartingaleCoupling} \mu  \nu  \pi  \iff  (\pi .\operatorname{map} \operatorname{Prod}.\operatorname{fst} \operatorname{measurablefst} = \mu  \land  \pi .\operatorname{map} \operatorname{Prod}.\operatorname{snd} \operatorname{measurablesnd} = \nu  \land  \operatorname{MeasureTheory}.\operatorname{Integrable} \operatorname{Prod}.\operatorname{fst} \pi .\operatorname{toMeasure} \land  \operatorname{MeasureTheory}.\operatorname{Integrable} \operatorname{Prod}.\operatorname{snd} \pi .\operatorname{toMeasure} \land  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{Measurable} \varphi  \to  (\exists  (\operatorname{M} : \mathbb{R} ), \forall  (\operatorname{x} : \mathbb{R} ), |\varphi  \operatorname{x}| \leq  \operatorname{M}) \to  \int  (\operatorname{p} : \mathbb{R}  \times  \mathbb{R} ), (\operatorname{p}.2 - \operatorname{p}.1) \cdot \varphi  \operatorname{p}.1 \operatorname{dmu} \pi .\operatorname{toMeasure} = 0)$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.IsMartingaleCoupling` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A tested martingale coupling has both exact marginals, integrable real coordinates, and vanishing displacement integral against every globally bounded measurable function of its first coordinate.

**Lemma 1.6 (fst_measure).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \mu  \nu  \pi  \to  (\operatorname{coe} \pi ).\operatorname{fst} = \operatorname{coe} \mu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.fst_measure` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The first measure marginal of a tested martingale coupling is the first specified law.

**Lemma 1.7 (snd_measure).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \mu  \nu  \pi  \to  (\operatorname{coe} \pi ).\operatorname{snd} = \operatorname{coe} \nu $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.snd_measure` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The second measure marginal of a tested martingale coupling is the second specified law.

**Lemma 1.8 (marginal_mean_eq).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \mu  \nu  \pi  \to  \mu .\operatorname{expect} \operatorname{id} = \nu .\operatorname{expect} \operatorname{id}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.marginal_mean_eq` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The two marginal means of a tested martingale coupling are equal.

**Lemma 1.9 (convex_expect_le).**

$$\forall  \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \} \{\pi  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )\}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \mu  \nu  \pi  \to  \forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \nu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \varphi  \to  \operatorname{ContinuousOn} \varphi  (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \mu .\operatorname{expect} \varphi  \leq  \nu .\operatorname{expect} \varphi $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.convex_expect_le` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Conditional Jensen gives the convex-test inequality using only convexity and continuity on the common compact interval.

**Definition 1.10 (DiscreteLaw).**

$$\operatorname{DiscreteLaw} = \{ (\operatorname{n} : \mathbb{N} ), (\operatorname{atom} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ), (\operatorname{weight} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ) | (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{n}), 0 \leq  \operatorname{weight} \operatorname{i}) \land  \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{n}), \operatorname{weight} \operatorname{i} = 1 \}$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.DiscreteLaw` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A finite real law consists of a natural cardinality, real atoms, and nonnegative real weights of total one. Zero weights and repeated atoms are allowed.

**Definition 1.11 (toProbDist).**

$$\forall  (\operatorname{p} : \operatorname{DiscreteLaw}), \operatorname{p}.\operatorname{toProbDist}.\operatorname{toMeasure} = \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{ENNReal}.\operatorname{ofReal} (\operatorname{p}.\operatorname{weight} \operatorname{i}) \operatorname{smul}  \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{dirac} (\operatorname{p}.\operatorname{atom} \operatorname{i})$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Finite weighted Dirac sums define genuine native probability laws; for a transition matrix the joint atom weights are the first-law weights multiplied by the transition entries.

**Lemma 1.12 (toProbDist_toMeasure).**

$$\forall  (\operatorname{p} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}), \operatorname{coe} \operatorname{p}.\operatorname{toProbDist} = \sum  \operatorname{i}, \operatorname{ENNReal}.\operatorname{ofReal} (\operatorname{p}.\operatorname{weight} \operatorname{i}) \operatorname{smul}  \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{dirac} (\operatorname{p}.\operatorname{atom} \operatorname{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist_toMeasure` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The underlying measure is the finite sum of weighted Dirac measures, with real nonnegative weights converted to ENNReal.

**Lemma 1.13 (toProbDist_supportsOn_of_atoms_mem).**

$$\forall  (\operatorname{p} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}) \{\operatorname{s} : \operatorname{Set} \mathbb{R} \}, \operatorname{MeasurableSet} \operatorname{s} \to  (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{atom} \operatorname{i} \in  \operatorname{s}) \to  \operatorname{p}.\operatorname{toProbDist}.\operatorname{supportsOn} \operatorname{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist_supportsOn_of_atoms_mem` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

If every listed atom belongs to a measurable set, the finite probability law assigns that set mass one.

**Definition 1.14 (mean).**

$$\forall  (\operatorname{p} : \operatorname{DiscreteLaw}), \operatorname{p}.\operatorname{mean} = \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} \cdot \operatorname{p}.\operatorname{atom} \operatorname{i}$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.mean` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The mean of a finite law is its weighted sum of atoms.

**Definition 1.15 (ConvexOrder).**

$$\forall  (\operatorname{p} \operatorname{q} : \operatorname{DiscreteLaw}), \operatorname{p}.\operatorname{ConvexOrder} \operatorname{q} \iff  \forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  \operatorname{Set}.\operatorname{univ} \varphi  \to  \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} \cdot \varphi  (\operatorname{p}.\operatorname{atom} \operatorname{i}) \leq  \sum  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \operatorname{q}.\operatorname{weight} \operatorname{j} \cdot \varphi  (\operatorname{q}.\operatorname{atom} \operatorname{j})$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.ConvexOrder` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Finite-law convex order compares weighted sums of every globally convex real test.

**Definition 1.16 (uniform).**

$$\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}) (\operatorname{x} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ), (\operatorname{uniform} \operatorname{n} \operatorname{hn} \operatorname{x}).\operatorname{n} = \operatorname{n} \land  (\operatorname{uniform} \operatorname{n} \operatorname{hn} \operatorname{x}).\operatorname{atom} = \operatorname{x} \land  (\operatorname{uniform} \operatorname{n} \operatorname{hn} \operatorname{x}).\operatorname{weight} = (\operatorname{fun} (\operatorname{i} : \operatorname{Fin} \operatorname{n}) \mapsto  1 / \operatorname{n})$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.uniform` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A positive finite cardinality and a real vector define the law with equal weights reciprocal to that cardinality.

**Lemma 1.17 (uniform_mean).**

$$\forall  \{\operatorname{n} : \mathbb{N} \} (\operatorname{hn} : 0 < \operatorname{n}) (\operatorname{x} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ), (\operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{uniform} \operatorname{n} \operatorname{hn} \operatorname{x}).\operatorname{mean} = (\sum  \operatorname{i}, \operatorname{x} \operatorname{i}) / \operatorname{coe} \operatorname{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.uniform_mean` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The mean of an equal-weight finite law is the arithmetic average of its atom vector.

**Definition 1.18 (BistochasticMartingaleMatrix).**

$$\forall  (\operatorname{p} \operatorname{q} : \operatorname{DiscreteLaw}), \operatorname{BistochasticMartingaleMatrix} \operatorname{p} \operatorname{q} = \{ (\operatorname{T} : \operatorname{Fin} \operatorname{p}.\operatorname{n} \to  \operatorname{Fin} \operatorname{q}.\operatorname{n} \to  \mathbb{R} ) | (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}) (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), 0 \leq  \operatorname{T} \operatorname{i} \operatorname{j}) \land  (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} \neq  0 \to  \sum  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \operatorname{T} \operatorname{i} \operatorname{j} = 1) \land  (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} \neq  0 \to  \sum  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \operatorname{T} \operatorname{i} \operatorname{j} \cdot \operatorname{q}.\operatorname{atom} \operatorname{j} = \operatorname{p}.\operatorname{atom} \operatorname{i}) \land  (\forall  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} \cdot \operatorname{T} \operatorname{i} \operatorname{j} = \operatorname{q}.\operatorname{weight} \operatorname{j}) \}$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.BistochasticMartingaleMatrix` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A transition matrix is nonnegative, has row sum one and the prescribed conditional mean on every positive-weight row, and has the exact weighted column marginal. Zero-weight rows impose no artificial row or mean restriction.

**Definition 1.19 (toJointProbDist).**

$$\forall  \{\operatorname{p} \operatorname{q} : \operatorname{DiscreteLaw}\} (\operatorname{M} : \operatorname{BistochasticMartingaleMatrix} \operatorname{p} \operatorname{q}), \operatorname{M}.\operatorname{toJointProbDist}.\operatorname{toMeasure} = \sum  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \sum  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \operatorname{ENNReal}.\operatorname{ofReal} (\operatorname{p}.\operatorname{weight} \operatorname{i} \cdot \operatorname{M}.\operatorname{T} \operatorname{i} \operatorname{j}) \operatorname{smul}  \operatorname{MeasureTheory}.\operatorname{Measure}.\operatorname{dirac} (\operatorname{p}.\operatorname{atom} \operatorname{i}, \operatorname{q}.\operatorname{atom} \operatorname{j})$$

*Formalization.* `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toJointProbDist` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Finite weighted Dirac sums define genuine native probability laws; for a transition matrix the joint atom weights are the first-law weights multiplied by the transition entries.

**Lemma 1.20 (isMartingaleCoupling).**

$$\forall  \{\operatorname{p} \operatorname{q} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}\} (\operatorname{M} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{BistochasticMartingaleMatrix} \operatorname{p} \operatorname{q}), \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \operatorname{p}.\operatorname{toProbDist} \operatorname{q}.\operatorname{toProbDist} \operatorname{M}.\operatorname{toJointProbDist}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.isMartingaleCoupling` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The weighted Dirac joint law built from such a matrix satisfies both actual marginals, coordinate integrability, and every bounded measurable martingale test.

**Theorem 1.21 (exists_martingaleCoupling_uniform).**

$$\forall  (\operatorname{p} \operatorname{q} : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}), 0 < \operatorname{p}.\operatorname{n} \to  \operatorname{p}.\operatorname{n} = \operatorname{q}.\operatorname{n} \to  (\forall  (\operatorname{i} : \operatorname{Fin} \operatorname{p}.\operatorname{n}), \operatorname{p}.\operatorname{weight} \operatorname{i} = 1 / \operatorname{coe} \operatorname{p}.\operatorname{n}) \to  (\forall  (\operatorname{j} : \operatorname{Fin} \operatorname{q}.\operatorname{n}), \operatorname{q}.\operatorname{weight} \operatorname{j} = 1 / \operatorname{coe} \operatorname{q}.\operatorname{n}) \to  \operatorname{p}.\operatorname{ConvexOrder} \operatorname{q} \to  \exists  (\pi  : \operatorname{ProbDist} (\mathbb{R}  \times  \mathbb{R} )), \operatorname{Econlib}.\operatorname{Probability}.\operatorname{IsMartingaleCoupling} \operatorname{p}.\operatorname{toProbDist} \operatorname{q}.\operatorname{toProbDist} \pi $$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.exists_martingaleCoupling_uniform` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Two positive equal-cardinality equal-weight finite laws in convex order have a genuine martingale coupling.

## References

- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.BistochasticMartingaleMatrix`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.ConvexOrder`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.DiscreteLaw`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.IsCoupling`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.IsMartingaleCoupling`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.convex_expect_le`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.exists_martingaleCoupling_uniform`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.fst_measure`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.fst_probability_marginal`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.isMartingaleCoupling`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.marginal_mean_eq`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.mean`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.snd_measure`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.snd_probability_marginal`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.supportsOn_Icc_prod`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toJointProbDist`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist_supportsOn_of_atoms_mem`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.toProbDist_toMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.uniform`
- Truth anchor: `D5/S3/Analytic/Probability/FiniteMartingaleCoupling.uniform_mean`
- Dependency: [D5/S3/Analytic/Convexity/FiniteMajorization](../Convexity/FiniteMajorization.md)
- Dependency: [D5/S3/Analytic/Probability/CompactConvexOrder](CompactConvexOrder.md)
- Dependency: [D5/S3/Geometry/ProbabilityTransport/CostCoupling](../../Geometry/ProbabilityTransport/CostCoupling.md)
