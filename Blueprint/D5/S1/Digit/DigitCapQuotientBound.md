# Quotient-digit bound for bounded-digit representations

## Abstract

At every radix, a digit cap below q times the radix allows at most q^m bounded-digit representations of an input below ell^(m+1).

**Theorem 1.1 (Uniform quotient-digit bound at every radix).**

Lean statement: `D5/S1/Digit/DigitCapQuotientBound.count_le_pow`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapQuotientBound.count_le_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural numbers ell, q, m, k and n with 2≤ell, 1≤q, k≤q·ell−1 and n<ell^(m+1), count k ell n≤q^m. Here count k ell n is the number of finitely supported functions a : Nat →₀ Nat with a(i)≤k for every i and Σ a(i)·ell^i=n; each function is counted once. The hypothesis 1≤q cannot be dropped: for q=0 the cap is zero, the input zero still has its empty representation, and 0^m=0 for m≥1.

Send a representation a to the m quotients a(i)/ell for i<m. Since a(i)≤k<q·ell, every quotient lies in {0,...,q−1}, so the target has q^m elements. Because n<ell^(m+1), every coefficient at a position above m vanishes, and a(m)·ell^m≤n forces a(m)<ell, so the top quotient is zero. If two representations have equal quotients, reducing their equal weighted sums modulo ell gives equal units remainders; with equal quotients the units digits agree. Cancelling them and dividing by ell leaves two equal shorter weighted sums, and induction recovers every digit. The map is therefore injective.

At radix four with q=2 this is the bound count k 4 n≤2^m for k≤6. The repunit family 1+4+...+4^m attains 2^m representations for k=5 and k=6, so the bound is sharp there.

## References

- Truth anchor: `D5/S1/Digit/DigitCapQuotientBound.count_le_pow`
- Dependency: [D5/S1/Digit/CoonsAdjacentGrowthRefutation](CoonsAdjacentGrowthRefutation.md)
