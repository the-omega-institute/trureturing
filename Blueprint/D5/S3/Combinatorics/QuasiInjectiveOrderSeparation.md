# Separating the Orders of Quasi-Injectivity

## Abstract

Every order has a function that is quasi-injective just below it and fails at it.

**Definition 1.1 (Quasi-injectivity of a given order).**

$$\forall f \in \mathrm{Nat} \to \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; (\operatorname{QuasiInjectiveOfOrder}\left(f, l\right)) \Leftrightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow ((k \le l) \Rightarrow (\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; (1 \le a) \Rightarrow ((1 \le b) \Rightarrow ((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (f^{(k)}(a \cdot n) = f^{(k)}(b \cdot n))) \Rightarrow (a = b))))))$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.QuasiInjectiveOfOrder` (`✓ std3`).

*Citation.* Prapanpong Pongsriiam (2021). *Quasi-Injectivity of Some Arithmetic Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf>.

*Commentary.*

Definition 1 of the source reads verbatim: "We call a function f : N to C a quasi-injective function if for all a, b in N, the condition f(an) = f(bn) for all n in N implies a = b. In addition, if f : N to N and l in N, then we say that f is quasi-injective of order l if f, f(2), f(3), ..., f(l) are quasi-injective, that is, for any a, b, k in N with 1 <= k <= l, if f(k)(an) = f(k)(bn) for all n in N, then a = b." Here the superscript denotes the k-fold composite. The source works with the positive integers, so the quantifiers over a, b and n carry positivity. Being quasi-injective of order l implies the same of every smaller order, so the orders form a decreasing chain of conditions.

**Definition 1.2 (The separating family).**

$$\forall m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (n = 1) \Rightarrow (\operatorname{g}\left(m, n\right) = 1)   ((n \ne 1) \land (\operatorname{mod}\left(n, 2\right) = 0)) \Rightarrow (\operatorname{g}\left(m, n\right) = 2 \cdot \left(m - 1\right) \cdot \operatorname{div}\left(n, 2\right) + 1)
((n \ne 1) \land ((\operatorname{mod}\left(n, 2\right) = 1) \land (\operatorname{mod}\left(\operatorname{div}\left(n - 1, 2\right), m - 1\right) = \operatorname{mod}\left(m - 2, m - 1\right)))) \Rightarrow (\operatorname{g}\left(m, n\right) = 1)   ((n \ne 1) \land ((\operatorname{mod}\left(n, 2\right) = 1) \land (\operatorname{mod}\left(\operatorname{div}\left(n - 1, 2\right), m - 1\right) \ne \operatorname{mod}\left(m - 2, m - 1\right)))) \Rightarrow (\operatorname{g}\left(m, n\right) = n + 2)$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an order m at least two, an odd number 2t+1 with t at least one is given the level t modulo m-1. The function raises the level by one, sends the top level to one, fixes one, and sends an even number 2t to the first level at 2(m-1)t+1. Division and remainder are the natural-number ones. Entering the ladder only through the even numbers is what makes the construction work: multiplying any a by two returns it to the entrance, so no property carried by a alone can trigger the collapse early. A level read from the exponent of two in n instead fails at once, since the pair a = 2 to the m-1 and b = 2 to the m already collapses under a single application.

**Definition 1.3 (The question asked of the orders).**

$$(claim) \Leftrightarrow (\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow (\exists f \in \mathrm{Nat} \to \mathrm{Nat},\; (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (1 \le \operatorname{f}\left(n\right))) \land ((\operatorname{QuasiInjectiveOfOrder}\left(f, m - 1\right)) \land (\neg (\operatorname{QuasiInjectiveOfOrder}\left(f, m\right))))))$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.claim` (`✓ std3`).

*Citation.* Prapanpong Pongsriiam (2021). *Quasi-Injectivity of Some Arithmetic Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf>.

*Commentary.*

Question 17 of the source reads verbatim: "For each m >= 2, is there a function f : N to N such that f is quasi-injective of order m - 1 but not of order m?" The statement displayed here is the affirmative reading, quantified over every order m at least two. The source proves that the divisor-counting function and the Jordan totient functions are quasi-injective of every order, and that the divisor-power sums are quasi-injective of order two, so no function it studies separates two consecutive orders.

**Theorem 1.4 (Consecutive orders are separated).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result` (`✓ std3`). ∎

*Resolves.* `Problems/quasi-injective-order-separation` (proved) by `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"quasi-injective-order-separation","declaration_gid":"D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The answer is yes, witnessed by the family above. Two facts drive it. First, for every k between one and m-1 and every t at least one, the k-fold composite sends 2t to 2((m-1)t + k - 1) + 1: the first step lands in level zero of the ladder and each later step raises the level by one, and level k-1 is below the top level whenever k is at most m-1, so the collapse is never reached. That value is strictly increasing in t, so taking n equal to two separates any two distinct a and b, which is quasi-injectivity of order m-1. Second, the m-fold composite is constantly one: an even number needs one step to enter the ladder, m-2 steps to climb it and one more to collapse, an odd number at level j needs m-j steps, and one is fixed. Hence the m-fold composite agrees on the multiples of one and of two while one and two differ, so quasi-injectivity of order m fails.

## References

- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.QuasiInjectiveOfOrder`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.claim`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.g`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.result`
