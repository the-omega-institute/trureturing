# The initial odd-wrap return gap at t=2

## Abstract

Three adjacent binomial growth bounds prove a strict initial odd-wrap return gap for every admissible p.

**Theorem 1.1 (At length 11p, the (3,3) quotient has fewer returns).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyInitialOddWrapSign.actual_initial_odd_wrap_sign`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyInitialOddWrapSign.actual_initial_odd_wrap_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every odd integer p at least 3, fix t=2 and m=11. Use the complete original relation lattices: the (1,9) generators are (p(m-1)/2,p(m+1)/2) and (p(m-9)/2,-p(m+9)/2), while the (3,3) generators are (p(m-3)/2,p(m+3)/2) and (p(m-3)/2,-p(m+3)/2). In each case F is the actual quotient map of the full integer span. The theorem proves W(F33,(11p).toNat)<W(F19,(11p).toNat) for the existing signed coordinate word count, retaining the entire original p domain.

Write P=p.toNat, so P is at least 3. The previously proved actual_odd_wrap_counts theorem at t=2 gives W19=2[choose(11P,6P)+choose(11P,10P)] and W33=4 choose(11P,7P). Binomial symmetry changes choose(11P,6P) to choose(11P,5P), and choose(11P,7P) to choose(11P,4P). It is therefore enough to prove 2 choose(11P,4P)<choose(11P,5P); the additional choose(11P,10P) term in W19 is nonnegative.

Let f(k)=choose(11P,k). The upstream identity Nat.choose_succ_right_eq gives f(k+1)(k+1)=f(k)(11P-k). At k=4P, 4P+1, and 4P+2, the assumption P>=3 supplies the three integer bounds 3f(4P)<=2f(4P+1), 4f(4P+1)<=3f(4P+2), and 5f(4P+2)<=4f(4P+3). These are the respective growth factors at least 3/2, 4/3, and 5/4, whose product is 5/2. Positivity of f(4P) therefore gives the strict inequality 2f(4P)<f(4P+3).

Since 4P+3<=5P and every intervening index remains below half of 11P, the existing Nat.choose_le_succ_of_lt_half_left inequality extends this bound to f(5P). Combining it with the exact actual quotient counts proves the source comparison for all odd integer p>=3.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyInitialOddWrapSign.actual_initial_odd_wrap_sign`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts](BajnokBeattyOddWrapReturnCounts.md)
