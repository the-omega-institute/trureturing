# ConditionalMeanAtoms

## Abstract

The atom in each equal-probability quantile bin is the conditional mean of that bin. Compact support keeps every atom inside the same closed interval. The construction is increasing, preserves the original mean, and identifies finite prefix sums with lower integrated quantiles.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Definition 1.1 (condMeanAtom).**

$$\forall  (\mu  : \operatorname{ProbDist} \mathbb{R} ) (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}) (\operatorname{k} : \operatorname{Fin} \operatorname{n}), \operatorname{condMeanAtom} \mu  \operatorname{n} \operatorname{hn} \operatorname{k} = \operatorname{n} \cdot \int  (\operatorname{u} : \mathbb{R} ) \operatorname{in} \operatorname{Set}.\operatorname{Ioc} (\operatorname{k} / \operatorname{n}) ((\operatorname{k} + 1) / \operatorname{n}), \mu .\operatorname{toMeasure}.\operatorname{quantile} \operatorname{u}$$

*Formalization.* `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Each atom is n times the integral of the generalized inverse over its equal-probability quantile bin, with right-closed left-open endpoints.

**Definition 1.2 (condMeanAtomize).**

$$\forall  (\mu  : \operatorname{ProbDist} \mathbb{R} ) (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}), \operatorname{condMeanAtomize} \mu  \operatorname{n} \operatorname{hn} = \operatorname{DiscreteLaw}.\operatorname{uniform} \operatorname{n} \operatorname{hn} (\operatorname{fun} (\operatorname{k} : \operatorname{Fin} \operatorname{n}) \mapsto  \operatorname{condMeanAtom} \mu  \operatorname{n} \operatorname{hn} \operatorname{k})$$

*Formalization.* `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize` (`✓ std3`).

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The conditional-mean atoms form an equal-weight finite law.

**Lemma 1.3 (integrableOn_quantile_bin).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \forall  \{\operatorname{n} : \mathbb{N} \}, 0 < \operatorname{n} \to  \forall  (\operatorname{k} : \operatorname{Fin} \operatorname{n}), \operatorname{MeasureTheory}.\operatorname{IntegrableOn} (\operatorname{coe} \mu ).\operatorname{quantile} (\operatorname{Set}.\operatorname{Ioc} (\operatorname{coe} \operatorname{coe} \operatorname{k} / \operatorname{coe} \operatorname{n}) ((\operatorname{coe} \operatorname{coe} \operatorname{k} + 1) / \operatorname{coe} \operatorname{n})) \operatorname{MeasureTheory}.\operatorname{volume}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanAtoms.integrableOn_quantile_bin` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Compact concentration makes the generalized inverse integrable over every positive-cardinality quantile bin.

**Lemma 1.4 (condMeanAtom_mem_Icc).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}) (\operatorname{k} : \operatorname{Fin} \operatorname{n}), \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtom} \mu  \operatorname{n} \operatorname{hn} \operatorname{k} \in  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom_mem_Icc` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Every conditional-mean atom remains in the original closed support interval, including a singleton interval.

**Lemma 1.5 (condMeanAtom_monotone).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \forall  \{\operatorname{n} : \mathbb{N} \} (\operatorname{hn} : 0 < \operatorname{n}), \operatorname{Monotone} \operatorname{fun} \operatorname{k} \mapsto  \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtom} \mu  \operatorname{n} \operatorname{hn} \operatorname{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom_monotone` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The conditional means of consecutive quantile bins form an increasing finite vector.

**Lemma 1.6 (condMeanAtomize_mean_eq).**

$$\forall  \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \operatorname{MeasureTheory}.\operatorname{Integrable} (\operatorname{fun} \operatorname{x} \mapsto  \operatorname{x}) \operatorname{coe} \mu  \to  \forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}), (\operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtomize} \mu  \operatorname{n} \operatorname{hn}).\operatorname{mean} = \mu .\operatorname{expect} \operatorname{id}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize_mean_eq` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Conditional-mean atomization preserves the original mean whenever the original coordinate is integrable.

**Lemma 1.7 (condMeanAtomize_partial_sum_eq).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \forall  \{\operatorname{n} : \mathbb{N} \} (\operatorname{hn} : 0 < \operatorname{n}) (\operatorname{K} : \operatorname{Fin} \operatorname{n}), \sum  \operatorname{i} \operatorname{with} \operatorname{coe} \operatorname{i} \leq  \operatorname{coe} \operatorname{K}, \operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtom} \mu  \operatorname{n} \operatorname{hn} \operatorname{i} = \operatorname{coe} \operatorname{n} \cdot \int  (\operatorname{u} : \mathbb{R} ) \operatorname{in} \operatorname{Set}.\operatorname{Ioc} 0 ((\operatorname{coe} \operatorname{coe} \operatorname{K} + 1) / \operatorname{coe} \operatorname{n}), (\operatorname{coe} \mu ).\operatorname{quantile} \operatorname{u}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize_partial_sum_eq` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Every lower prefix sum of conditional-mean atoms is n times the integrated quantile up to the end of that prefix.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom_mem_Icc`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtom_monotone`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize_mean_eq`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.condMeanAtomize_partial_sum_eq`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanAtoms.integrableOn_quantile_bin`
- Dependency: [D5/S3/Analytic/Probability/CompactConvexOrder](CompactConvexOrder.md)
- Dependency: [D5/S3/Analytic/Probability/CompactQuantile](CompactQuantile.md)
- Dependency: [D5/S3/Analytic/Probability/FiniteMartingaleCoupling](FiniteMartingaleCoupling.md)
