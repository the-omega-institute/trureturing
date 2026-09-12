# Two-item greedy allocation and exchange

## Abstract

Explicit two-item allocations turn a change of order into a comparison of real expressions.

Let I be any type with decidable equality, a and b distinct elements of I, w a real function on I, and B a real budget. Write g with subscript ab for greedyFill(w,[a,b],B), and g with subscript ba for the reversed list. The notation ite(P,x,y) means x when P holds and y otherwise. Define the two quantities L and R below. No sign restriction is imposed for the allocation identities; real division is total, with division by zero equal to zero.

$L = \operatorname{ite}\left(\operatorname{w}\left(a\right)\le B, 1, \frac{B}{\operatorname{w}\left(a\right)}\right), R = \operatorname{ite}\left(\operatorname{w}\left(a\right)\le B, \operatorname{ite}\left(\operatorname{w}\left(b\right)\le B-\operatorname{w}\left(a\right), 1, \frac{B-\operatorname{w}\left(a\right)}{\operatorname{w}\left(b\right)}\right), 0\right)$

**Theorem 1.1 (The complete two-item allocation).**

$$\forall i:I, g_{ab}(i) = \operatorname{ite}\left(i=a, L, \operatorname{ite}\left(i=b, R, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function equals L at a, R at b, and zero at every other index. Expanding the two recursive steps and evaluating the two function updates gives the identity. The order of the tests preserves the first coordinate even while the second step is evaluated.

**Theorem 1.2 (The first coordinate).**

$$g_{ab}(a) = \operatorname{ite}\left(\operatorname{w}\left(a\right)\le B, 1, \frac{B}{\operatorname{w}\left(a\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a the allocation is one if w(a) is at most B, and B/w(a) otherwise. This is evaluation of the complete allocation at its first index.

**Theorem 1.3 (The second coordinate).**

$$g_{ab}(b) = \operatorname{ite}\left(\operatorname{w}\left(a\right)\le B, \operatorname{ite}\left(\operatorname{w}\left(b\right)\le B-\operatorname{w}\left(a\right), 1, \frac{B-\operatorname{w}\left(a\right)}{\operatorname{w}\left(b\right)}\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At b the allocation is zero when the first item does not fit. Otherwise it is one if w(b) is at most B-w(a), and (B-w(a))/w(b) if it is larger. Distinctness of a and b lets the second coordinate pass the first index test.

**Theorem 1.4 (The return as a real expression).**

$$\operatorname{V}\left(g_{ab}\right) = \operatorname{ite}\left(\operatorname{w}\left(a\right)\le B, \operatorname{v}\left(a\right)+\operatorname{ite}\left(\operatorname{w}\left(b\right)\le B-\operatorname{w}\left(a\right), \operatorname{v}\left(b\right), \frac{\operatorname{v}\left(b\right)}{\operatorname{w}\left(b\right)}(B-\operatorname{w}\left(a\right))\right), \frac{\operatorname{v}\left(a\right)}{\operatorname{w}\left(a\right)}B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GreedyFillPair.objective_greedyFill_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now assume I is finite and let v be any real function on I. Define V(t) as the sum over I of v(i)t(i), the objective. The support identity reduces this sum to a and b. Substituting the two coordinate identities and rearranging multiplication gives the displayed formula, still without sign assumptions.

**Theorem 1.5 (Ordering by return per unit weight).**

$$0<\operatorname{w}\left(a\right) \land 0<\operatorname{w}\left(b\right) \land 0\le B \land \frac{\operatorname{v}\left(b\right)}{\operatorname{w}\left(b\right)}\le\frac{\operatorname{v}\left(a\right)}{\operatorname{w}\left(a\right)} \implies \operatorname{V}\left(g_{ba}\right) \le \operatorname{V}\left(g_{ab}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite I and distinct a and b, suppose both listed weights are positive, B is nonnegative, and v(b)/w(b) is at most v(a)/w(a). Then putting a first cannot decrease the return. The returns may have either sign, and no condition is needed on unlisted weights. If both items fit together the returns coincide. Otherwise the increase is the density difference multiplied by w(a)+w(b)-B when both fit separately, by the weight of the sole item that fits when just one fits, and by B when neither fits. Each multiplier is nonnegative. Equal densities therefore give equal returns for both orders.

## References

- Truth anchor: `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair`
- Truth anchor: `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_left`
- Truth anchor: `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_right`
- Truth anchor: `D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_swap`
- Truth anchor: `D5/S3/Analytic/Knapsack/GreedyFillPair.objective_greedyFill_pair`
- Dependency: [D5/S3/Analytic/Knapsack/FractionalKnapsackDual](FractionalKnapsackDual.md)
