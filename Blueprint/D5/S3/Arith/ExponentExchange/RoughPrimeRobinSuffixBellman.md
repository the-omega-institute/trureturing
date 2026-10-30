# Same-integer Robin suffix maxima

## Abstract

Finite Robin suffix maxima retain the accumulated integer in every denominator.

Use q, S, W, F and Rough from RoughPrimeSuffixBellman: q(y,i) is the i-th prime above y, S(y,i,t) is its consecutive prime-power product, W(y,i,t) is its normalized sigma product, and F(y,i,b,h,t) means Ordered(h,t) and S(y,i,t) <= b. All number variables are natural numbers and t is a finite list of natural exponents. Write L(x) = log(log(x)), with natural x cast into the reals, and Z(n) = sigma1(n)/n. The score R(C,y,i,t) is W(y,i,t)/L(C S(y,i,t)). T(C,y,i,b,h) denotes robinV: the semantic maximum of this score over the finite feasible list set when b >= 1, and zero otherwise. The maximum is noncomputable; no numerical evaluation is asserted.

A(C,y,i,b,h) denotes robinBranchValues. It contains the terminal value 1/L(C), and G(q(y,i),a) T(C q(y,i)^a,y,i+1,div(b,q(y,i)^a),a) for every natural a with 1 <= a <= h and q(y,i)^a <= b. Here G(q,a) is the reciprocal geometric sum and div is natural division. Thus both the accumulated integer and the remaining budget change on a branch. Multiplicative reassociation preserves the exact integer C S in the nonlinear denominator.

**Theorem 1.1 (Exact branches and attainment).**

$$\begin{aligned}\forall     C  , y  , i  , b  , h   : \mathbb{N} ,  1 \le b \Rightarrow [ \\T\left(C, y, i, b, h\right) = max\left(A\left(C, y, i, b, h\right)\right) \\\land ( \forall   t : List\left(\mathbb{N}\right) ,  F\left(y, i, b, h, t\right) \Rightarrow R\left(C, y, i, t\right) \le T\left(C, y, i, b, h\right) ) \\\land ( \exists   t : List\left(\mathbb{N}\right) ,  F\left(y, i, b, h, t\right) \land R\left(C, y, i, t\right) = T\left(C, y, i, b, h\right) ) \\\land ( \forall     a   : \mathbb{N} ,  1 \le a \land q\left(y, i\right)^{a} \le b \Rightarrow div\left(b, q\left(y, i\right)^{a}\right) < b ) ] \end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.robin_bellman_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state with positive budget, the four clauses give the finite branch equation, the upper bound for every actual feasible suffix, an attaining feasible suffix, and strict budget descent. The branch identity uses the same full integer in the parent and child score. Nonnegativity of G transports each child's attained maximum even without a sign assumption on L.

**Theorem 1.2 (Finite rough-integer score bound).**

$$\forall     C  , y  , B  , n   : \mathbb{N} ,  3 \le C \land 1 \le y \land 1 \le n \le B \land Rough\left(y, n\right) \Rightarrow \frac{Z\left(n\right)}{L\left(C \cdot n \right)} \le T\left(C, y, 0, B, c\left(y, B\right)\right) $$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.rough_robin_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cap c(y,B) is the reused rootCap, Nat.log(q(y,0),B). At the individual budget n, rough_prime_suffix_complete supplies an ordered representative m <= n with W >= Z(n). Since C >= 3 and m >= 1, L(C m) is positive and no larger than L(C n). Dividing in the correct direction therefore bounds the score at the original integer by that of an actual feasible suffix. Increasing the budget and root cap places this suffix in the finite root state, where robin_bellman_complete supplies its bound. This theorem gives a finite comparison, not a uniform numerical Robin threshold or a proof of RH.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.robin_bellman_complete`
- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman.rough_robin_bound`
- Dependency: [D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman](RoughPrimeSuffixBellman.md)
