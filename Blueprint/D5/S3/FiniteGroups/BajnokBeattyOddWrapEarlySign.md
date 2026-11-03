# A uniform early return gap at the first odd wrap

## Abstract

An exact weighted binomial recurrence proves an early cone of strict return gaps for the original quotients.

**Theorem 1.1 (The (3,3) quotient has fewer returns when 3t is at most 2p+1).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapEarlySign.actual_early_odd_wrap_sign`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapEarlySign.actual_early_odd_wrap_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers with p at least 3, p odd, t at least 2, and 3t<=2p+1. Put m=6t-1 and L=(pm).toNat. The (1,9) relation lattice is the full integer span of (p(m-1)/2,p(m+1)/2) and (p(m-9)/2,-p(m+9)/2); the (3,3) lattice is the full span of (p(m-3)/2,p(m+3)/2) and (p(m-3)/2,-p(m+3)/2). For their actual quotient maps, the theorem proves W(F33,L)<W(F19,L), retaining the original signed coordinate word domain and all displayed parameter assumptions.

Set P=p.toNat, N=(p(6t-1)).toNat, b=(p(3t-2)).toNat, and d=(p(3t-5)).toNat. The exact integer bridges give N=2b+3P and b+P<=2P^2. For the binomial row f(k)=choose(N,k), all indices from b to b+P lie below its midpoint, so the existing Nat.choose_le_succ_of_lt_half_left inequality gives f(k)>=f(b) and nonnegative increments. Nat.choose_succ_right_eq gives, at k=b+i, the exact identity [f(k+1)-f(k)](k+1)=f(k)(3P-2i-1).

Since k+1<=b+P and the numerator is nonnegative for 0<=i<P, each step gives f(b)(3P-2i-1)<=[f(k+1)-f(k)](b+P). The proof accumulates these inequalities by induction on r<=P, maintaining the exact partial weight r(3P-r). At r=P this yields f(b)2P^2<=[f(b+P)-f(b)](b+P). Using b+P<=2P^2 and cancelling the strictly positive b+P proves 2f(b)<=f(b+P).

The existing actual_odd_wrap_counts theorem gives W19=2[choose(N,p(3t))+choose(N,p(3t+4))] and W33=4 choose(N,p(3t+1)), with the integer lower indices converted by toNat. Binomial symmetry reflects these three indices to b+P, d, and b respectively. The index d lies between zero and N, so Nat.choose_pos gives f(d)>0. Consequently 2f(b)<f(b+P)+f(d), which is exactly the strict actual return comparison after multiplication by two.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapEarlySign.actual_early_odd_wrap_sign`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts](BajnokBeattyOddWrapReturnCounts.md)
