# Localized prime weight and exact ramp separation

## Abstract

An exact ramp decomposition and smooth branches of the prime weight localized at a moving cutoff.

**Definition 1.1 (Localized weight).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight at P,s,t is log(1+exp(-s*abs(log(t/P)))).

**Definition 1.2 (Finite prime remainder).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.remainder`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.remainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remainder is the sum of the localized weight over all primes at most the natural floor of x.

**Theorem 1.3 (Nonnegative localized weight).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The localized weight is nonnegative for all real P,s,t.

**Theorem 1.4 (Continuity away from zero).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and a>0, the localized weight is continuous on every closed real interval [a,b], for every real s.

**Definition 1.5 (Smooth left extension).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left extension subtracts s*(log(P)-log(t)) from log(1+P^s/t^s).

**Theorem 1.6 (Left-branch identity).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_eq_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_eq_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0,t<=P, the smooth left extension equals the localized weight.

**Theorem 1.7 (Right-branch identity).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_eq_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_eq_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0,P<=t, log(1+P^s/t^s) equals the localized weight.

**Theorem 1.8 (Left-branch derivative).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0 and every real s, the left extension has derivative s/t-abelKernel(s,P^s,t).

**Theorem 1.9 (Left endpoint value at the peak).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and every real s, the smooth left extension at t=P equals log(2).

**Theorem 1.10 (Right endpoint value at the peak).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_at_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_at_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0 and every real s, log(1+P^s/P^s) equals log(2).

**Theorem 1.11 (Increasing left branch).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,t>0,s>=0, the left-branch derivative s/t-abelKernel(s,P^s,t) is nonnegative.

**Theorem 1.12 (Exact finite prime ramp decomposition).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.prime_weight_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.prime_weight_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>0,P<=x,s>=0, the sum over primes p<=x of log(1+P^s*p^(-s)) equals s*(primeCount(P)*log(P)-theta(P))+remainder(P,s,x). The natural-floor endpoints and the prime at the cutoff are retained exactly. This supports an upper bound at the second distinct-prime threshold; a matching lower bound has not been established.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_at_cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_deriv_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.leftWeight_eq_weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.prime_weight_split`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.remainder`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_at_cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.rightWeight_eq_weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_continuousOn`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight.weight_nonneg`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion](PrimeExpansion.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
