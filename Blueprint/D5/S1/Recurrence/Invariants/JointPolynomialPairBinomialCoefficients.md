# The Joint Polynomial Pair of OEIS A208342

## Abstract

Schulte's binomial sum gives every coefficient in the jointly generated polynomial pair.

All indices and values are natural numbers. The operators natSub and natDiv mean truncated subtraction and integer division. The function ite chooses its second or third argument according to its first argument, and binomial is the natural binomial coefficient.

**Definition 1.1 (The joint coefficient recursion).**

$$\begin{aligned}(\forall i \in Nat, \operatorname{first}\left(\operatorname{coefficientPair}\left(0\right), i\right) = \operatorname{ite}\left(i = 0, 1, 0\right) \land \operatorname{second}\left(\operatorname{coefficientPair}\left(0\right), i\right) = \operatorname{ite}\left(i = 0, 1, 0\right))\\(\forall n, i \in Nat, \operatorname{first}\left(\operatorname{coefficientPair}\left(n + 1\right), i\right) = \operatorname{first}\left(\operatorname{coefficientPair}\left(n\right), i\right) + \operatorname{ite}\left(i = 0, 0, \operatorname{second}\left(\operatorname{coefficientPair}\left(n\right), \operatorname{natSub}\left(i, 1\right)\right)\right) \land \operatorname{second}\left(\operatorname{coefficientPair}\left(n + 1\right), i\right) = \operatorname{ite}\left(i = 0, 0, \operatorname{first}\left(\operatorname{coefficientPair}\left(n\right), \operatorname{natSub}\left(i, 1\right)\right) + \operatorname{second}\left(\operatorname{coefficientPair}\left(n\right), \operatorname{natSub}\left(i, 1\right)\right)\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.coefficientPair` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A208342, Triangle of coefficients of polynomials u(n,x) jointly generated with A208343*. URL: <https://oeis.org/A208342>.

*Commentary.*

At stage zero both coefficient functions equal one at degree zero and zero elsewhere. The two step equations are the coefficient forms of u(n,x)=u(n-1,x)+x*v(n-1,x) and v(n,x)=x*u(n-1,x)+x*v(n-1,x).

**Definition 1.2 (Coefficients of the first polynomial).**

$$\forall n, i \in Nat, \operatorname{u}\left(n, i\right) = \operatorname{first}\left(\operatorname{coefficientPair}\left(\operatorname{natSub}\left(n, 1\right)\right), i\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.u` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A208342, Triangle of coefficients of polynomials u(n,x) jointly generated with A208343*. URL: <https://oeis.org/A208342>.

*Commentary.*

The stage shift makes u(1,x) the initial constant polynomial one.

**Definition 1.3 (Coefficients of the companion polynomial).**

$$\forall n, i \in Nat, \operatorname{v}\left(n, i\right) = \operatorname{second}\left(\operatorname{coefficientPair}\left(\operatorname{natSub}\left(n, 1\right)\right), i\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.v` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A208342, Triangle of coefficients of polynomials u(n,x) jointly generated with A208343*. URL: <https://oeis.org/A208342>.

*Commentary.*

The same stage shift makes v(1,x) the initial constant polynomial one.

**Definition 1.4 (The A208342 triangle entry).**

$$\forall n, k \in Nat, \operatorname{T}\left(n, k\right) = \operatorname{u}\left(n, \operatorname{natSub}\left(k, 1\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.T` (`✓ std3`).

*Citation.* Werner Schulte (2017). *OEIS A208342, Triangle of coefficients of polynomials u(n,x) jointly generated with A208343*. URL: <https://oeis.org/A208342>.

*Commentary.*

The entry T(n,k) is the coefficient of x^(k-1) in u(n,x).

**Theorem 1.5 (Schulte's binomial coefficient formula).**

$$\forall n, k \in Nat, 0 < k \Rightarrow \left(k \le n \Rightarrow \operatorname{T}\left(n, k\right) = \sum_{j = 0}^{\operatorname{natDiv}\left(\operatorname{natSub}\left(k, 1\right), 2\right)} \operatorname{binomial}\left(\operatorname{natSub}\left(\operatorname{natSub}\left(k, 1\right), j\right), j\right) \cdot \operatorname{binomial}\left(\operatorname{natSub}\left(n, k\right) + j, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.schulte_a208342` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a208342-joint-polynomial-pair-binomial-coefficients` (proved) by `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.schulte_a208342`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a208342-joint-polynomial-pair-binomial-coefficients","declaration_gid":"D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.schulte_a208342","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2017). *OEIS A208342, Triangle of coefficients of polynomials u(n,x) jointly generated with A208343*. URL: <https://oeis.org/A208342>.

*Commentary.*

Simultaneous induction gives closed forms for both coefficient functions. The two recursion components use different Pascal summation transformations. Vanishing binomial coefficients remove every term above natDiv(k-1,2), leaving the displayed finite sum.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.T`
- Truth anchor: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.coefficientPair`
- Truth anchor: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.schulte_a208342`
- Truth anchor: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.u`
- Truth anchor: `D5/S1/Recurrence/Invariants/JointPolynomialPairBinomialCoefficients.v`
