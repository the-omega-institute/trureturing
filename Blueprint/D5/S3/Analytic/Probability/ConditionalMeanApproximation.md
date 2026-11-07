# ConditionalMeanApproximation

## Abstract

Conditional-mean atomization converges weakly to the original compactly supported law and preserves convex order simultaneously for each pair. The final approximation theorem supplies equal positive cardinalities, uniform weights, interval membership of all atoms, and both weak limits.

The construction of Daniel Lyng in Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f is adapted under Apache-2.0. Apache-2.0 license: docs/reports/licenses/econlib-strassen/LICENSE.txt. Strassen (1965) provides the historical martingale-transport context. In formulas, coe denotes the canonical coercion, dmu the integration measure, iUnion indexed union, smul scalar multiplication, and ae almost everywhere. Namespace-qualified Lean names and interval constructors retain their mathematical meaning; separated identifier words denote the corresponding underscored Lean constant.

**Theorem 1.1 (condMeanAtomize_tendsto).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \mu .\operatorname{supportsOn} (\operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \to  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} (\operatorname{n} : \mathbb{N} ) \mapsto  (\operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtomize} \mu  (\operatorname{n} + 1) (\operatorname{Nat}.\operatorname{succpos} \operatorname{n})).\operatorname{toProbDist}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \mu )$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanApproximation.condMeanAtomize_tendsto` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

The conditional-mean finite laws with n plus one bins converge weakly to the original compactly supported probability law.

**Theorem 1.2 (condMeanAtomize_convexOrder).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \operatorname{ConvexOrderOnIcc} \operatorname{a} \operatorname{b} \mu  \nu  \to  \forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{hn} : 0 < \operatorname{n}), (\operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtomize} \mu  \operatorname{n} \operatorname{hn}).\operatorname{ConvexOrder} (\operatorname{Econlib}.\operatorname{Probability}.\operatorname{DiscreteLaw}.\operatorname{condMeanAtomize} \nu  \operatorname{n} \operatorname{hn})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanApproximation.condMeanAtomize_convexOrder` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

Applying the same positive bin count to both members of an interval convex-order pair preserves finite-law convex order.

**Theorem 1.3 (exists_discrete_approximation).**

$$\forall  \{\operatorname{a} \operatorname{b} : \mathbb{R} \} \{\mu  \nu  : \operatorname{Econlib}.\operatorname{Probability}.\operatorname{ProbDist} \mathbb{R} \}, \operatorname{ConvexOrderOnIcc} \operatorname{a} \operatorname{b} \mu  \nu  \to  \exists  (\operatorname{p} \operatorname{q} : \mathbb{N}  \to  \operatorname{DiscreteLaw}), (\forall  (\operatorname{n} : \mathbb{N} ), (\operatorname{p} \operatorname{n}).\operatorname{ConvexOrder} (\operatorname{q} \operatorname{n})) \land  (\forall  (\operatorname{n} : \mathbb{N} ), 0 < (\operatorname{p} \operatorname{n}).\operatorname{n}) \land  (\forall  (\operatorname{n} : \mathbb{N} ), (\operatorname{p} \operatorname{n}).\operatorname{n} = (\operatorname{q} \operatorname{n}).\operatorname{n}) \land  (\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{i} : \operatorname{Fin} (\operatorname{p} \operatorname{n}).\operatorname{n}), (\operatorname{p} \operatorname{n}).\operatorname{weight} \operatorname{i} = 1 / \operatorname{coe} (\operatorname{p} \operatorname{n}).\operatorname{n}) \land  (\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{j} : \operatorname{Fin} (\operatorname{q} \operatorname{n}).\operatorname{n}), (\operatorname{q} \operatorname{n}).\operatorname{weight} \operatorname{j} = 1 / \operatorname{coe} (\operatorname{q} \operatorname{n}).\operatorname{n}) \land  (\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{i} : \operatorname{Fin} (\operatorname{p} \operatorname{n}).\operatorname{n}), (\operatorname{p} \operatorname{n}).\operatorname{atom} \operatorname{i} \in  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \land  (\forall  (\operatorname{n} : \mathbb{N} ) (\operatorname{j} : \operatorname{Fin} (\operatorname{q} \operatorname{n}).\operatorname{n}), (\operatorname{q} \operatorname{n}).\operatorname{atom} \operatorname{j} \in  \operatorname{Set}.\operatorname{Icc} \operatorname{a} \operatorname{b}) \land  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  (\operatorname{p} \operatorname{n}).\operatorname{toProbDist}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \mu ) \land  \operatorname{Filter}.\operatorname{Tendsto} (\operatorname{fun} \operatorname{n} \mapsto  (\operatorname{q} \operatorname{n}).\operatorname{toProbDist}) \operatorname{Filter}.\operatorname{atTop} (\operatorname{nhds} \nu )$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ConditionalMeanApproximation.exists_discrete_approximation` (`✓ std3`). ∎

*Citation.* Daniel Lyng (2026). *Econlib compact scalar Strassen construction*. URL: <https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Probability/Order/Strassen.lean>.

*Commentary.*

A compact convex-order pair admits paired finite approximations in convex order with positive equal cardinalities, equal weights, all atoms in the interval, and both prescribed weak limits.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanApproximation.condMeanAtomize_convexOrder`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanApproximation.condMeanAtomize_tendsto`
- Truth anchor: `D5/S3/Analytic/Probability/ConditionalMeanApproximation.exists_discrete_approximation`
- Dependency: [D5/S3/Analytic/Probability/ConditionalMeanAtoms](ConditionalMeanAtoms.md)
