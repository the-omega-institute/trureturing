# Zelinsky's question on the values of the first difference

## Abstract

Norton threshold first differences omit a positive integer.

**Definition 1.1 (Every positive integer is proposed as a difference).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.claim`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

For every natural m>0, claim asks for a natural starting index n>=1 such that a(n+1)-a(n)=m. Here a is the least positive length of consecutive prime Euler factors whose product strictly exceeds two. The difference in claim uses natural subtraction. This is Question 5 in Section 5 of Zelinsky's Integers 21 article A76.

**Theorem 1.2 (Some positive integer is omitted).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-norton-first-difference` (refuted) by `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-norton-first-difference","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

The proposition claim is false: there is a positive natural integer m that equals no a(n+1)-a(n) with n>=1.

The adjacent-cancellation estimate at alpha=2 bounds one plus the real first difference below by a positive constant times p_n. Chebyshev's prime-counting upper bound then gives a(n+1)-a(n)>=2*n for every sufficiently large natural n.

Choose a natural N beyond that threshold. If every positive value occurred, each of the values 1 through 2*N+1 would have a preimage among the indices 1 through N: any later index has difference at least 2*(N+1). The image of N indices cannot contain 2*N+1 distinct values. This contradiction gives the omitted positive integer without specifying a particular one.

The conclusion is the negation of the universal value assertion. It neither identifies all omitted values nor states an exact asymptotic for the first differences.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.result`
- Dependency: [D5/S3/Arith/Abundancy/BeriZelinskyQuestion6](BeriZelinskyQuestion6.md)
