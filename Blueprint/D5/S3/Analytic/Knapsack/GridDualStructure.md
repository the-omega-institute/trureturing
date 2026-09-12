# Finite grid duality and optimal fill structure

## Abstract

Finite two-point grids have an exact fractional linear program, and every fractional optimum matches its row density as a dual price.

Let I be any finite index type. For each i, let c(i) and d(i) be real endpoints. Write f(x)=log(1-exp(-x)), h(i)=d(i)-c(i), Delta(i)=f(d(i))-f(c(i)), rho(i)=Delta(i)/h(i), and R=M-sum c(i). The feasible set F consists of real-valued functions a on I with 0<=a(i)<=1 and sum h(i)a(i)<=R. These constraints use only an upper expected coordinate-sum budget.

$\operatorname{h}\left(i\right) = \operatorname{d}\left(i\right)-\operatorname{c}\left(i\right), R = M-\sum_{i \in I} \operatorname{c}\left(i\right)$

Write V(a)=sum [f(c(i))+a(i)Delta(i)] and D(p)=p M+sum max(f(c(i))-p c(i),f(d(i))-p d(i)). The grid dual G is the infimum of D(p) over nonnegative real prices p. Optimal(a) means that a is feasible and V(a) equals the supremum of V over F.

**Theorem 1.1 (The exact fractional linear program).**

$$G = \operatorname{sup}_{a \in F} \operatorname{V}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GridDualStructure.grid_dual_eq_fill_sup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<c(i)<d(i) for every i and sum c(i)<=M. Then G equals the supremum of V on F. Subtracting the lower endpoints gives positive weights h, positive returns Delta, and nonnegative budget R. The fractional-knapsack strong duality theorem applies to these data. Translation by the constant sum f(c(i)) carries its supremum and price infimum to the displayed equality. The index type may be empty.

**Theorem 1.2 (Strict improvement with spare budget).**

$$\exists b \in F, \operatorname{V}\left(a\right) < \operatorname{V}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GridDualStructure.slack_fill_improvable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a belongs to F, a(j)<1, h(j)>0, Delta(j)>0, and sum h(i)a(i)<R. There is a feasible b with V(a)<V(b). No positivity assumption is imposed on other rows in this assertion. Increase coordinate j by epsilon=min(1-a(j),(R-sum h(i)a(i))/h(j)), leaving all other coordinates fixed. Both entries of this minimum are positive. Its two upper bounds preserve the box and budget constraints, and the return increases by Delta(j)epsilon>0.

**Theorem 1.3 (A fractional optimum saturates the budget).**

$$\sum_{i \in I} \operatorname{h}\left(i\right)\operatorname{a}\left(i\right) = R$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_saturates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<c(i)<d(i) for all i, Optimal(a), and 0<a(j)<1. Then sum h(i)a(i)=R. Strict monotonicity of f on positive reals gives Delta(j)>0. A strict budget inequality would permit the preceding improvement and contradict attainment of the supremum. This assertion applies to every optimal fill and does not require an extreme-point hypothesis.

**Theorem 1.4 (The fractional row supplies an attaining price).**

$$p = \operatorname{rho}\left(j\right) > 0, \operatorname{D}\left(p\right) = G$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_matching_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<c(i)<d(i) for every i, Optimal(a), and 0<a(j)<1. Put p=rho(j). Then p>0, each row satisfies (1-a(i))(f(c(i))-p c(i))+a(i)(f(d(i))-p d(i))=max(f(c(i))-p c(i),f(d(i))-p d(i)), every full row has rho(i)>=p, every empty row has rho(i)<=p, and D(p)=G.

A greedy certificate supplies an attaining nonnegative price. Optimality of a identifies its return with the certificate value. Budget saturation then makes the sum of nonnegative row dual gaps zero, so every row gap is zero. At the strictly fractional row, this equality forces Delta(j)-p h(j)=0. Substitution yields the claimed price, the row maxima, and both density inequalities. Ties are retained by the non-strict inequalities; no uniqueness of the fractional row is needed.

## References

- Truth anchor: `D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_matching_price`
- Truth anchor: `D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_saturates`
- Truth anchor: `D5/S3/Analytic/Knapsack/GridDualStructure.grid_dual_eq_fill_sup`
- Truth anchor: `D5/S3/Analytic/Knapsack/GridDualStructure.slack_fill_improvable`
- Dependency: [D5/S3/Analytic/Interpolation/TwoPointGridDominance](../Interpolation/TwoPointGridDominance.md)
- Dependency: [D5/S3/Analytic/Knapsack/FractionalKnapsackDual](FractionalKnapsackDual.md)
