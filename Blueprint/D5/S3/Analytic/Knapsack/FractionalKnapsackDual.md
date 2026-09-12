# Fractional knapsack and its dual price

## Abstract

A decreasing return-to-weight ratio orders a greedy maximizer, and a threshold price attains the dual minimum.

Let I be an arbitrary finite index type with decidable equality, and let w and v be real functions on I. Write C for cost, V for return, D for the scalar dual value, and F for the feasible set at a real budget B. For the first two theorems, assume that all weights are strictly positive, all returns are nonnegative, and B is nonnegative.

$\operatorname{C}\left(t\right) = \sum_{i \in I} \operatorname{w}\left(i\right)\operatorname{t}\left(i\right), \operatorname{V}\left(t\right) = \sum_{i \in I} \operatorname{v}\left(i\right)\operatorname{t}\left(i\right), \operatorname{D}\left(p\right) = pB+\sum_{i \in I} \max(0,\operatorname{v}\left(i\right)-p\operatorname{w}\left(i\right))$

$F = \{t:I \to \mathbb{R} \mid (\forall i \in I, 0 \le \operatorname{t}\left(i\right) \le 1) \land \operatorname{C}\left(t\right) \le B\}$

**Theorem 1.1 (Equality of primal and dual values).**

$$\operatorname{sup}_{t \in F} \operatorname{V}\left(t\right) = \operatorname{inf}_{p \ge 0} \operatorname{D}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.fractional_knapsack_strong_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every weight is strictly positive, every return is nonnegative, and B is nonnegative. Then the supremum of the return over F equals the infimum of D over nonnegative real prices. This equality refers only to the original weights, returns and budget; no ordering of I is a hypothesis. The infimum ranges over the type of nonnegative real prices.

**Theorem 1.2 (A greedy allocation and a minimizing price).**

$$\exists l:\operatorname{List}\left(I\right), \exists p:\mathbb{R}, \operatorname{Nodup}\left(l\right) \land \operatorname{set}\left(l\right) = I \land \operatorname{Sorted}\left(l\right) \land g_{l} \in F \land 0 \le p \land p(B-\operatorname{C}\left(g_{l}\right)) = 0 \land (\forall i \in I, (\operatorname{v}\left(i\right)-p\operatorname{w}\left(i\right))g_{l}(i) = \max(0,\operatorname{v}\left(i\right)-p\operatorname{w}\left(i\right))) \land \operatorname{V}\left(g_{l}\right) = \operatorname{D}\left(p\right) \land \operatorname{sup}_{t \in F} \operatorname{V}\left(t\right) = \operatorname{V}\left(g_{l}\right) \land \operatorname{inf}_{p \ge 0} \operatorname{D}\left(p\right) = \operatorname{V}\left(g_{l}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.greedy_attains_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positive-weight, nonnegative-return and nonnegative-budget assumptions, there is a list l containing each index exactly once and a nonnegative price p. Sorted(l) means that whenever i precedes j in l, v(j)/w(j) is at most v(i)/w(i). The notation g with subscript l denotes greedyFill(w,l,B).

The greedy rule starts with remaining budget B. An empty list gives the zero allocation. If the first weight does not exceed the remaining budget, that item receives one and the rule continues on the tail with that weight subtracted. Otherwise the first item receives the fraction theta equal to the remaining budget divided by its weight, and every later item receives zero. Positivity of the weight and the stopping inequality give zero less than or equal to theta and theta strictly less than one.

Induction by the largest ratio constructs both the list and the price. When the budget stops within the first item, use that item's ratio as the price. Every remaining item's reduced return is nonpositive. When the first item is filled, use the price constructed for the tail. That price is either zero or the ratio of a tail item, so it is at most the first ratio. These two cases give the coordinate identities and the budget identity displayed above.

For every feasible allocation t and nonnegative price p, the coordinate bounds give (v(i)-p w(i))t(i) at most max(0,v(i)-p w(i)). Summing and applying the budget inequality gives V(t) at most D(p). The constructed allocation attains equality because the coordinate identities sum exactly and p times the unused budget is zero. Thus the primal supremum is a maximum and the dual infimum is a minimum. Empty index sets and zero budgets are included.

**Theorem 1.3 (Enough budget to fill every item).**

$$e \in F \land \operatorname{sup}_{t \in F} \operatorname{V}\left(t\right) = \sum_{i \in I} \operatorname{v}\left(i\right) \land \operatorname{inf}_{p \ge 0} \operatorname{D}\left(p\right) = \sum_{i \in I} \operatorname{v}\left(i\right) \land \operatorname{D}\left(0\right) = \sum_{i \in I} \operatorname{v}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.full_budget_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For this assertion the weights and budget may be arbitrary real numbers: it suffices that every return is nonnegative and the sum of the weights is at most B. Writing e for the constant-one allocation, e belongs to F, both optimal values are the sum of all returns, and price zero attains that value. Indeed the constant-one allocation is feasible and D(0) equals its return. The general upper bound then settles both extrema.

## References

- Truth anchor: `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.fractional_knapsack_strong_duality`
- Truth anchor: `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.full_budget_optimum`
- Truth anchor: `D5/S3/Analytic/Knapsack/FractionalKnapsackDual.greedy_attains_duality`
