# FiniteMajorization

## Abstract

Finite real-vector convex domination yields a doubly stochastic matrix carrying the larger vector to the smaller one. Prefix sums of increasing vectors give convex domination. The proof constructs the majorization relation and consumes pinned Mathlib Birkhoff theory; it is not a second proof of Birkhoff.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Lemma 1.1 (convexOn_hinge_right).**

$$\forall  (\operatorname{a} : \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  \operatorname{Set}.\operatorname{univ} \operatorname{fun} \operatorname{z} \mapsto  \operatorname{max} (\operatorname{z} - \operatorname{a}) 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FiniteMajorization.convexOn_hinge_right` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The positive-part excess over a fixed real threshold is convex on the whole real line.

**Theorem 1.2 (exists_doublyStochastic_mulVec_of_convex_dominates).**

$$\forall  \{\operatorname{n} : \mathbb{N} \} (\operatorname{x} \operatorname{y} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ), (\forall  (\varphi  : \mathbb{R}  \to  \mathbb{R} ), \operatorname{ConvexOn} \mathbb{R}  \operatorname{Set}.\operatorname{univ} \varphi  \to  \sum  \operatorname{i}, \varphi  (\operatorname{x} \operatorname{i}) \leq  \sum  \operatorname{j}, \varphi  (\operatorname{y} \operatorname{j})) \to  \sum  \operatorname{i}, \operatorname{x} \operatorname{i} = \sum  \operatorname{j}, \operatorname{y} \operatorname{j} \to  \exists  \operatorname{D} \in  \operatorname{doublyStochastic} \mathbb{R}  (\operatorname{Fin} \operatorname{n}), \operatorname{D}.\operatorname{mulVec} \operatorname{y} = \operatorname{x}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FiniteMajorization.exists_doublyStochastic_mulVec_of_convex_dominates` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Convex domination and equal total sums for two finite real vectors yield a doubly stochastic matrix taking the second vector to the first. Empty vectors are included.

**Theorem 1.3 (sum_convex_le_of_partial_sum_ge).**

$$\forall  \{\operatorname{n} : \mathbb{N} \} (\operatorname{x} \operatorname{y} : \operatorname{Fin} \operatorname{n} \to  \mathbb{R} ), \operatorname{Monotone} \operatorname{x} \to  \operatorname{Monotone} \operatorname{y} \to  \sum  \operatorname{i}, \operatorname{x} \operatorname{i} = \sum  \operatorname{i}, \operatorname{y} \operatorname{i} \to  (\forall  (\operatorname{K} : \operatorname{Fin} \operatorname{n}), \sum  \operatorname{i} \operatorname{with} \operatorname{coe} \operatorname{i} \leq  \operatorname{coe} \operatorname{K}, \operatorname{y} \operatorname{i} \leq  \sum  \operatorname{i} \operatorname{with} \operatorname{coe} \operatorname{i} \leq  \operatorname{coe} \operatorname{K}, \operatorname{x} \operatorname{i}) \to  \forall  \{\varphi  : \mathbb{R}  \to  \mathbb{R} \}, \operatorname{ConvexOn} \mathbb{R}  \operatorname{Set}.\operatorname{univ} \varphi  \to  \sum  \operatorname{i}, \varphi  (\operatorname{x} \operatorname{i}) \leq  \sum  \operatorname{i}, \varphi  (\operatorname{y} \operatorname{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/FiniteMajorization.sum_convex_le_of_partial_sum_ge` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

For increasing finite vectors of equal total sum, domination of every lower prefix sum implies the inequality for every globally convex real test.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/FiniteMajorization.convexOn_hinge_right`
- Truth anchor: `D5/S3/Analytic/Convexity/FiniteMajorization.exists_doublyStochastic_mulVec_of_convex_dominates`
- Truth anchor: `D5/S3/Analytic/Convexity/FiniteMajorization.sum_convex_le_of_partial_sum_ge`
