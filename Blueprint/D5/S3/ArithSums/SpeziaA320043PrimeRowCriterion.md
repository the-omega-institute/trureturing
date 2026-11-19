# The prime-row square criterion for A320043

## Abstract

For a prime p≥5, the A320043 value a(p−1) is a perfect square exactly when p²−12y²=1 has a solution y≥1, and then a(p−1)=(py)².

**Theorem 1.1 (Square values on prime rows).**

Lean statement: `D5/S3/ArithSums/SpeziaA320043PrimeRowCriterion.prime_row_square_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SpeziaA320043PrimeRowCriterion.prime_row_square_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a(n)=Σ_{k=1}^{n}(n+1−k)²k/gcd(n+1−k,k)³. For every prime p≥5, a(p−1) is the square of a natural number if and only if p²−12y²=1 for some natural y≥1; moreover every natural y with p²−12y²=1 gives a(p−1)=(py)², so the nonnegative square root is py.

Every k in 1..p−1 is coprime to p−k, so the quotients are the plain products (p−k)²k, and a telescoping cubic sum gives 12·a(p−1)=p²(p²−1). If p²−12y²=1, then 12·a(p−1)=12p²y² and a(p−1)=(py)². Conversely, if a(p−1)=m², then p divides 12m²; since p≥5 does not divide 12=2²·3, p divides m. Writing m=py and cancelling p² gives 12y²=p²−1, and y≥1 because p²−1≥24.

## References

- Truth anchor: `D5/S3/ArithSums/SpeziaA320043PrimeRowCriterion.prime_row_square_iff`
- Dependency: [D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation](SpeziaA320043SquareValuesRefutation.md)
