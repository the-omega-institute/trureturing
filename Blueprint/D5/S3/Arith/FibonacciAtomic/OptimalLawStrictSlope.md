# Strict Growth of the Optimal Real-law Slope

## Abstract

The minimum ratio of dyadic sampling cost to least atom mass grows strictly with the label count.

Simplex(m,p) means that p is a real vector indexed by Fin m with sum one; PositiveLaw adds strict positivity of every coordinate. LeastIndex(p,k) means p(k) is at most every coordinate. R(p,d) is 2^d minus the sum of the integer floors of 2^d p(i), and L(p) is the sum of R(p,d)/2^d over all natural depths. These definitions include terminating binary coordinates and all real probability laws.

**Theorem 1.1 (Normalized floor tails).**

$$\forall m, p, \operatorname{Simplex}\left(m,p\right) \to ((\forall d, 0 \le \operatorname{R}\left(p,d\right) \le m) \land \operatorname{Summable}\left(d\mapsto\frac{\operatorname{R}\left(p,d\right)}{2^{d}}\right) \land 0 \le \operatorname{L}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.law_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The floor inequalities bound each residual between zero and the number of coordinates. Geometric domination makes the tail series summable and its sum nonnegative.

**Theorem 1.2 (The first charged bit).**

$$\forall m, p, (2 \le m \land \operatorname{PositiveLaw}\left(m,p\right)) \to 1 \le \operatorname{L}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.cost_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at least two positive coordinates, every coordinate is below one. All depth-zero floors vanish, so the depth-zero contribution is one.

**Theorem 1.3 (Every law bounds the infimum).**

$$\forall m, p, k, (\operatorname{PositiveLaw}\left(m,p\right) \land \operatorname{LeastIndex}\left(p,k\right)) \to \operatorname{alpha}\left(m\right) \le \frac{\operatorname{L}\left(p\right)}{\operatorname{p}\left(k\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All admissible ratios are nonnegative. The infimum is therefore at most the ratio of any particular positive normalized law.

**Theorem 1.4 (A lower bound from the least mass).**

$$\forall m, (2 \le m) \to m \le \operatorname{alpha}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_ge_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least coordinate is at most 1/m and the cost is at least one. Every admissible ratio, and hence its infimum, is at least m.

**Theorem 1.5 (Lower semicontinuity on the positive simplex).**

$$\forall m, k, \operatorname{LowerSemicontinuousOn}\left(p\mapsto\frac{\operatorname{L}\left(p\right)}{\operatorname{p}\left(k\right)},\operatorname{PositiveSimplex}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.ratio_lower_semicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a fixed law, finitely many floors cannot increase in a sufficiently small neighborhood. Every finite tail prefix supplies a local lower bound. Convergence of the nonnegative series and continuity of the positive denominator pass this bound to the full ratio.

**Theorem 1.6 (Attainment in the full real domain).**

$$\forall m, (2 \le m) \to \exists p, k, \operatorname{PositiveLaw}\left(m,p\right) \land \operatorname{LeastIndex}\left(p,k\right) \land \frac{\operatorname{L}\left(p\right)}{\operatorname{p}\left(k\right)} = \operatorname{alpha}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform law supplies a finite comparison ratio. Since every multi-label law costs at least one, any smaller ratio has its least coordinate bounded away from zero. After relabeling this coordinate to a fixed index, optimization takes place on a nonempty compact subset of the real simplex. Lower semicontinuity supplies a minimum there, and laws outside it have larger ratio.

**Theorem 1.7 (Strict growth with the number of labels).**

$$\operatorname{alpha}\left(1\right) = 0 \land \operatorname{alpha}\left(2\right) = 2 \land (\forall m: \mathbb{N}, (3 \le m) \to \operatorname{alpha}\left((m - 1)\right) < \operatorname{alpha}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a strictly positive normalized real law p on m labels, the dyadic cost is the sum over depths d of the unassigned floor remainder divided by 2^d. The function alpha is the infimum of this cost divided by the smallest mass. The domain contains all such real laws, without a rationality or finite-depth restriction.

A single label has zero cost. For two labels, the cost is at least one and the smallest mass is at most one half. The uniform two-label law has cost one and attains ratio two.

Take an attaining law with at least three labels. Merging two atoms never increases any floor remainder. If the smallest atom is unique, merging it with another atom strictly raises the new minimum mass. If two atoms have the same smallest mass, their first positive binary digit produces a strict carry one depth earlier, so merging them strictly reduces the convergent cost sum. In each case the new law has a strictly smaller ratio, proving the strict inequality for consecutive label counts.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_ge_labels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.alpha_le`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.attained`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.cost_ge_one`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.law_data`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.ratio_lower_semicontinuous`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
