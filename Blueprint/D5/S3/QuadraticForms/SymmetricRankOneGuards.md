# Polynomial guards and finite candidate shifts

## Abstract

Uncancelled integer polynomial guards propagate the zero-nullity scalar state and give a finite exact set of candidate shifts.

Use a common real shift x and integer polynomials P(i), Q(i) for the child response ratios. At a proper cotree leaf with parent label q take P = −1 and Q = X + q. At an internal node of label c with parent label q use t = c − q, with join labeled 1, union labeled 2, and q = 0 at the root.

An induction using the degree and propagation statements gives monic subtree guards and nullity zero at shifts outside their root union. At a candidate shift use the exact flagged, resonant or nonresonant transition at the same shift in every block. The union includes poles and counts coincident roots once.

**Definition 1.1 (Common response numerator).**

$$P=\sum \operatorname{P}\left(i\right) \prod_{j \neq i} \operatorname{Q}\left(j\right)$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum over all child indices i. In the ith summand the product is over all j other than i.

**Definition 1.2 (Uncancelled output guard).**

$$Q=R+tP$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseGuard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R is the product of all child guards over the integer polynomial ring. The coupling adds t times the common numerator P to R.

**Theorem 1.3 (Scalar propagation at a common shift).**

$$k=0 \land \operatorname{Response}\left(U, u, \frac{\operatorname{P}\left(x\right)}{\operatorname{Q}\left(x\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneGuards.update_block_of_guard_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite family of finite-dimensional real symmetric blocks with product direction u. At x every child guard and the output guard must be nonzero. If each child has zero nullity and response P(i)(x)/Q(i)(x), then the real coupling by the integer t has zero nullity and response P(x)/Q(x). The ratio comes from the nonresonant update of the block sum.

**Theorem 1.4 (Guard and numerator degrees).**

$$\operatorname{deg}\left(P\right)=N-1 \land \operatorname{lc}\left(P\right)=-N \land \operatorname{Monic}\left(Q\right) \land \operatorname{deg}\left(Q\right)=N$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseGuard_degrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite child family, suppose each size n(i) is positive, Q(i) is monic of natural degree n(i), and P(i) has natural degree n(i) − 1 and leading coefficient −n(i). The displayed N is the sum of those sizes. The coefficient sum is −N, and adding the lower-degree term tP preserves the monic leading term of R.

**Definition 1.5 (Distinct real roots of the guards).**

$$C=\cup_{i \in s} \operatorname{roots}\left(\operatorname{Q}\left(i\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneGuards.realGuardCandidates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each guard is mapped from the integers to the reals before its roots are taken, and root multiplicities are discarded. The polynomial roots operation gives the empty multiset for the zero polynomial. The criterion below assumes every guard in s is nonzero.

**Theorem 1.6 (The finite exact shift criterion).**

$$\operatorname{card}\left(C\right) \leq \sum \operatorname{deg}\left(\operatorname{Q}\left(i\right)\right) \land ((\exists x, \operatorname{target}\left(x\right)) \iff (\exists x \in C, \operatorname{target}\left(x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneGuards.realGuardCandidates_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All guards indexed by s are nonzero polynomials. Assume the target predicate fails at every real x where all those guards are nonzero. The sum runs over s, and the existential equivalence uses the same target at each candidate, including eligibility and saturation when those form the target. The finite set is a mathematical real-root criterion.

## References

- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.realGuardCandidates`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.realGuardCandidates_spec`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseGuard`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseGuard_degrees`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.responseNumerator`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneGuards.update_block_of_guard_ne_zero`
- Dependency: [D5/S3/QuadraticForms/SymmetricRankOneKernel](SymmetricRankOneKernel.md)
