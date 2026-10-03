# Integer-rank capacity and prefix slack

## Abstract

Finite distinct integer ranks admit a defect-sensitive capacity bound and an exact nonnegative prefix slack.

Let I be a finite set of natural numbers, r a positive natural number, A and N nonnegative real numbers, and c a function from the natural numbers to the reals. Every d in I satisfies r<=d, 0<=c(d)<=A d, and sum over I of c(d)<=N. The ranks are distinct because I is a set; the hypotheses concern total mass at each rank, not separate contributions sharing a rank. All natural-number ranks in real expressions are cast to the reals.

$\operatorname{x}\left(d\right) = \frac{\operatorname{c}\left(d\right)}{d}, J = \sum_{d \in I} \operatorname{x}\left(d\right), B = \sum_{d \in I} \operatorname{c}\left(d\right), D = \sum_{d \in I} \operatorname{x}\left(d\right)(A-\operatorname{x}\left(d\right)), C = (2r-1)A$

Write x(d)=c(d)/d, J for total occupancy, B for total mass, D for the sum of coordinate defects, C=(2r-1)A, g(d) for the strict-prefix gap, and H for the occupancy-weighted prefix slack. The function xtilde on natural numbers equals x(i) for i in I and zero otherwise. The interval [r,d) in every formula is the finite natural-number interval, including its lower endpoint and excluding its upper endpoint.

$\operatorname{g}\left(d\right) = A(d-r)-\sum_{i \in I, i < d} \operatorname{x}\left(i\right), H = \sum_{d \in I} \operatorname{x}\left(d\right) \operatorname{g}\left(d\right)$

**Theorem 1.1 (Defect-sensitive capacity and exact prefix saturation).**

$$\forall I: \operatorname{Finset}\left(\operatorname{Nat}\left(\right)\right), r: \operatorname{Nat}\left(\right), A,N: \operatorname{Real}\left(\right), c: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right), (0 < r, 0 \le A, 0 \le N, (\forall d \in I: r \le d, 0 \le \operatorname{c}\left(d\right) \le Ad), \sum_{d \in I} \operatorname{c}\left(d\right) \le N) \implies (B = \sum_{d \in I} d\operatorname{x}\left(d\right), 0 \le D, J^2+CJ+D \le 2AB \le 2AN, 0 \le C^2+8AN-4D, J \le \frac{\sqrt{C^2+8AN-4D}-C}{2} \le \frac{\sqrt{C^2+8AN}-C}{2}, J^2+CJ+D+2H = 2AB, 0 \le H, (\forall d \in I: \operatorname{g}\left(d\right) = \sum_{i \in [r,d)} (A-\operatorname{xtilde}\left(i\right)) \ge 0), (0 < A \implies (H = 0 \iff \forall d \in I, 0 < \operatorname{x}\left(d\right) \implies \forall i \in [r,d): i \in I \land \operatorname{x}\left(i\right) = A)), (A = 0 \implies H = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/IntegerRankCapacityDefect.integer_rank_capacity_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all data satisfying the stated hypotheses and definitions, B equals sum d x(d), D is nonnegative, and J squared plus C J plus D is at most 2 A B, which is at most 2 A N. The defect-adjusted radicand C squared plus 8 A N minus 4 D is nonnegative. J is bounded by its quadratic root, and that root itself is bounded by the root with D omitted.

The exact identity is J squared plus C J plus D plus 2 H equals 2 A B. Every prefix gap equals the sum of A-xtilde(i) over the natural-number interval [r,d), and each gap and H are nonnegative. If A>0, H=0 if and only if every active rank d, meaning x(d)>0, has every natural number i in [r,d) present in I with x(i)=A. This imposes no saturation requirement on the last active rank itself. If A=0, H=0 without any additional membership conclusion.

Induct on the maximum rank a. The old rank set is contained in [r,a), so its cardinality is at most a-r and its total occupancy J0 is at most (a-r)A. Adding x=x(a) increases the square, linear term, and coordinate defect together by 2x(J0+rA), at most the new budget 2Aax. This proves the capacity inequality from distinct integer ranks rather than assuming a prefix-mass bound. Completing the square and using nonnegative J and C gives the first root bound; nonnegative D and monotonicity of the square root give the root-to-root comparison.

$J0 \le (a-r)A, 2x(J0+rA) \le 2Aax$

No old prefix changes when the maximum rank is inserted. H increases by x times (A(a-r)-J0), exactly accounting for the unused increment of the main budget and proving the identity by the same maximum-rank induction. Missing prefix ranks contribute A to the gap, while present ranks contribute A-x(i). These terms are nonnegative. When A>0, a zero sum at an active rank excludes missing ranks and forces all its strict-prefix coordinates to equal A; the converse follows by evaluating each weighted gap.

The empty set, A=0, and N=0 are permitted. Each of these cases has J=D=H=0, and the displayed capacity and root inequalities remain valid. No infinite-rank statement, repeated-index capacity, or endpoint saturation is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Knapsack/IntegerRankCapacityDefect.integer_rank_capacity_defect`
