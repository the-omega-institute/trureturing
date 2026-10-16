# The stationary signed Parry law

## Abstract

The stationary signed Parry law.

**Theorem 1.1 (Finite suffix recurrence).**

Lean statement: `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_succ`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k:Nat, p:Real, j:Fin k and hj:j.val+1<k, suffixWeight k p j=p+p*suffixWeight k p (j.val+1). Splitting the finite geometric sum into its first term and tail proves the recurrence. It supports the stationary law and the right Perron weight of the original Reset beam trace.

**Theorem 1.2 (Last suffix).**

Lean statement: `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_last`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k:Nat, p:Real, j:Fin k and hj:not(j.val+1<k), suffixWeight k p j=p. The remaining finite sum has length one. This is the terminal case of the stationary and Perron recurrences.

**Theorem 1.3 (The stationary signed Parry law).**

Lean statement: `D5/S3/TotalVariation/ParryResetLaw.parry_stationary_law`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryResetLaw.parry_stationary_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k >= 2, set p = parryParameter k = (dbonacciPerronRoot k)^(-1), h_j = suffixWeight k p j, S = normalizer k, and pi(s) = parryLaw k s = p^(s.2.val) h_(s.2) / (2S). Then 1/2 < p <= Real.goldenRatio^(-1) and rootSum k p = sum over a in range k of p^(a+1) = 1. For every j in Fin k, p <= h_j <= 1, and S >= 1. Every entry of K = kernel k p is nonnegative, every row of K sums to one, and pi(s) >= 0 for every state s. The law is normalized, sum_s pi(s) = 1; it is stationary, with sum_s pi(s) K(s,t) = pi(t) for every t; and it is invariant under sign complement: pi(flip(s)) = pi(s) for every s.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryResetLaw.parry_stationary_law`
- Truth anchor: `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_last`
- Truth anchor: `D5/S3/TotalVariation/ParryResetLaw.suffixWeight_succ`
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../../S0/Tower/DBonacci/PerronRoot.md)
- Dependency: [D5/S3/TotalVariation/TwistedResetPaths](TwistedResetPaths.md)
