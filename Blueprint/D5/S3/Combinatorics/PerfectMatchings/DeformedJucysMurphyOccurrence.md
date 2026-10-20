# The Common Coefficient in Coulter–Do Conjecture 5.8

## Abstract

The literal differential operator and native matching operator use exactly one occurrence coefficient on every partition.

Work in the infinite polynomial algebra on the positive power sums. For a partition rho, p(rho) has the literal part multiplicities as exponents. B(b,rho,sigma) denotes the coefficient of p(sigma) in the literal ordered differential operator D_b(p(rho)); R(b,rho,sigma) denotes the canonical native rowCoefficient. The proof first extends the exponent encoding to arbitrary positive residual multisets, including the empty multiset. A derivative is a sum over erased occurrences. Two derivatives erase distinct occurrences in order, retaining repeated and equal parts.

**Theorem 1.1 (Literal Coefficients Equal Canonical Native Occurrences).**

$$\forall K \in CharZeroField,\; \forall b \in K,\; \forall k \in Nat,\; \forall rho \in \operatorname{Partition}\left(k\right),\; \forall sigma \in \operatorname{Partition}\left(k\right),\; \operatorname{B}\left(b, rho, sigma\right) = \operatorname{R}\left(b, rho, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.operatorCoefficient_eq_rowCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For cuts, the two derivative indices correspond bijectively to the positive ordered displacement d with 0<d<r. Both equal halves and complementary cuts remain. For joins, the second occurrence belongs to rho with the first occurrence erased. The diagonal identity is choose(r,2)=r(r-1)/2. Coefficient extraction separates distinct partitions by exponent injectivity. These arguments include zero coefficients, singleton ranges and empty residual monomials, without a correspondence premise.

Now K=RatFunc Complex, beta=X, alpha=1+X and A(rho)=alpha^(number of parts)*product_r r^(multiplicity r)*(multiplicity r)!. Every A(rho) is nonzero. Define c_lambda(mu)=R(beta,mu,lambda).

The coefficient equality also transports the algebraic detailed balance to the native coefficient: A(sigma)*R(beta,rho,sigma) equals A(rho)*R(beta,sigma,rho), including unrelated zero branches. The live C2 proof applies the algebraic normalized expansion directly through the coefficient equality; no separate transported balance theorem is needed.

**Theorem 1.2 (C2 with Exactly the C1 Coefficient).**

$$\forall k \in Nat,\; \forall lambda \in \operatorname{Partition}\left(k\right),\; \sum_{mu\in\operatorname{Partition}\left(k\right)}{{\frac{\operatorname{c}\left(lambda, mu\right)}{\operatorname{A}\left(mu\right)}}\cdot{\operatorname{p}\left(mu\right)}} = \operatorname{D}\left({\frac{1}{\operatorname{A}\left(lambda\right)}}\cdot{\operatorname{p}\left(lambda\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.same_coefficient_C2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Divide balance by the two nonzero normalizations and use the literal operator's homogeneous partition expansion. The coefficient remains R(beta,mu,lambda), in the native C1 orientation.

**Theorem 1.3 (The Original Joint Native and Polynomial Statement).**

$$\forall k \in \operatorname{PositiveNat}\left(\right),\; \forall lambda \in \operatorname{Partition}\left(k\right),\; \operatorname{UniqueCommonCoefficient}\left(k, lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.conjecture58` (`✓ std3`). ∎

*Resolves.* `Problems/coulter-do-2025-conjecture-5-8` (proved) by `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.conjecture58`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"coulter-do-2025-conjecture-5-8","declaration_gid":"D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.conjecture58","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

UniqueCommonCoefficient means that there is exactly one function c from all partitions of k to K for which S_beta(indicator lambda)(p)=c(ct(p)) for every actual native matching p, and the displayed C2 identity holds with c(mu) in its numerator. Existence uses native_C1 and same_coefficient_C2 with c(mu)=R(beta,mu,lambda). Uniqueness uses matching_realization at each partition mu and evaluates the native function equality at that actual matching. Thus no partition is silently excluded or assigned an unconstrained coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.conjecture58`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.operatorCoefficient_eq_rowCoefficient`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.same_coefficient_C2`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2](DeformedJucysMurphyC2.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRealization](DeformedJucysMurphyRealization.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow](DeformedJucysMurphyRow.md)
