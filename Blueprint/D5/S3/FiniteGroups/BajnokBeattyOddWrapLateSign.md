# A late strict return gap at the first odd wrap

## Abstract

A finite binomial recurrence gives a sufficient cone for a strict gap between the actual odd-wrap return counts.

**Theorem 1.1 (The (1,9) quotient has fewer returns when 6t exceeds 9p+1).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapLateSign.actual_late_odd_wrap_sign`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapLateSign.actual_late_odd_wrap_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p at least 3, p odd, t at least 2, and 9p+1<6t. Put m=6t-1 and L=(pm).toNat. Use the full original lattices: for (1,9) the generators are (p(m-1)/2,p(m+1)/2) and (p(m-9)/2,-p(m+9)/2); for (3,3) they are (p(m-3)/2,p(m+3)/2) and (p(m-3)/2,-p(m+3)/2). In each case F is the actual quotient map of the integer span. The theorem proves W(F19,L)<W(F33,L) for all signed coordinate words. In particular t at least 2p satisfies the displayed cone condition; no sign conclusion outside this domain is asserted.

The existing exact odd-wrap theorem supplies W19=2(A+D) and W33=4B, where n=p(6t-1), a=3pt, A=choose(n,a), B=choose(n,a+p), and D=choose(n,a+4p). All indices from a to a+4p lie on the decreasing half of the same binomial row and remain at most n. The proof reuses Nat.choose_succ_right_eq for the adjacent-index recurrence and Nat.choose_pos for positivity. It uses no asymptotic approximation or numerical parameter sweep.

Write f(k)=choose(n,k) and delta(k)=f(k)-f(k+1). Since n=2a-p, the exact recurrence is delta(k)(k+1)=f(k)(2k+1-n), with nonnegative differences. On k=a+i for 0<=i<p, use f(k)<=A and k+1>=a; the numerator sum is exactly 2p^2, yielding A(a-2p^2)<=Ba. On k=a+p+i for 0<=i<3p, use f(k)>=D and k+1<=a+4p; the numerator sum is exactly 18p^2, yielding D(a+4p+18p^2)<=B(a+4p).

Set u=a-2p^2 and v=a+4p+18p^2. The cone makes both positive and gives the exact strict surplus 2uv-av-(a+4p)u=8p^3(6t-1-9p)>0. Multiplying the two weighted count bounds by v and u respectively and adding, then using B>0, proves (A+D)uv<2Buv. Cancelling the positive product gives A+D<2B and hence the actual return gap. This is a sufficient domain established by a finite recurrence proof; optimality of its boundary and literature novelty are not claimed.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapLateSign.actual_late_odd_wrap_sign`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts](BajnokBeattyOddWrapReturnCounts.md)
