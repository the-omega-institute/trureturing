# Finite ordered Strassen coupling

## Abstract

Finite-poset upper-set inequalities characterize ordered nonnegative couplings of equal-mass functions.

Let alpha be any finite partial order, including the empty carrier. The real functions p and q are pointwise nonnegative and have equal total mass; that mass can be zero and is not normalized to one. An upper finset U contains every y above any x in U. A coupling is a nonnegative matrix whose row and column sums are exactly p and q and whose entries vanish unless x <= y.

**Theorem 1.1 (Upper-set inequalities if and only if an ordered coupling exists).**

$$\forall (alpha: Type*), [\operatorname{Fintype}(alpha)] [\operatorname{PartialOrder}(alpha)] \forall (p: alpha \to \mathbb{R}), \forall (q: alpha \to \mathbb{R}), (\forall (x: alpha), 0 \leq \operatorname{p}(x)) \Rightarrow (\forall (x: alpha), 0 \leq \operatorname{q}(x)) \Rightarrow (\sum_{x: alpha} (\operatorname{p}(x)) = \sum_{x: alpha} (\operatorname{q}(x))) \Rightarrow ((\forall (U: \operatorname{Finset}(alpha)), (\forall (x: alpha), \forall (y: alpha), (x \in U) \Rightarrow (x \leq y) \Rightarrow y \in U) \Rightarrow \sum_{x \in U} (\operatorname{p}(x)) \leq \sum_{x \in U} (\operatorname{q}(x))) \iff (\exists (pi: alpha \to \left(alpha \to \mathbb{R}\right)), (\forall (x: alpha), \forall (y: alpha), 0 \leq \operatorname{pi}(x, y)) \land ((\forall (x: alpha), \sum_{y: alpha} (\operatorname{pi}(x, y)) = \operatorname{p}(x)) \land ((\forall (y: alpha), \sum_{x: alpha} (\operatorname{pi}(x, y)) = \operatorname{q}(y)) \land (\forall (x: alpha), \forall (y: alpha), (\neg (x \leq y)) \Rightarrow \operatorname{pi}(x, y) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/FiniteOrderedStrassen.forall_isUpperSet_sum_le_iff_exists_coupling` (`✓ std3`). ∎

*Citation.* Unattributed source file; copyright Meta Platforms, Inc. and affiliates (2026). *Finite Strassen stochastic domination in ATLAS Lean*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/StrassenCoupling.lean>.

*Commentary.*

The hard direction follows the retained ATLAS proof by strong induction on a finite-carrier measure combining carrier size with the counts of nonzero p and q entries. Zero p-mass on the carrier forces zero q-mass by nonnegativity and equal totals, and the zero matrix settles this case, including the empty carrier.

If a nonempty proper upper set U is tight, with equal p- and q-mass on U, restrict both functions to U and to its complement in the carrier. An upper set V of the complement gives an upper set V union U of the original carrier; subtracting the tight equality transfers the inequality to V. Both subcarriers are smaller. Add their couplings to recover the original marginals and support.

When there is no such tight cut, choose a with p(a) > 0. The upper cone of a and its inequality give b >= a with q(b) > 0. Moving t units from p(a) and q(b) preserves every upper-set inequality precisely when t does not exceed the slack of each upper set containing b but not a. If the smallest relevant slack is below min(p(a),q(b)), push that amount to make a nonempty proper upper cut tight and split there. Otherwise push min(p(a),q(b)); at least one nonzero support entry disappears, decreasing the induction measure. Adding t back at (a,b) restores the original marginals and order support.

For the converse, order support makes every row starting in an upper set stay inside that set. Sum the row identities over U, commute the finite sums, and bound the restricted column sums by the full q columns using entrywise nonnegativity. The theorem imposes no unit-mass, nonempty-carrier, linear-order or Boolean-configuration restriction, and asserts no martingale condition or algorithm.

This is a native integration of a known classical result from the immutable ATLAS Lean source, not a new mathematical theorem. The source and license correspondence, scope of the narrow transplant, and adopted-pin retirement condition are recorded in the Library note. Possible finite Markov and configuration uses have not been measured or completed here.

## References

- Truth anchor: `D5/S3/Analytic/Probability/FiniteOrderedStrassen.forall_isUpperSet_sum_le_iff_exists_coupling`
