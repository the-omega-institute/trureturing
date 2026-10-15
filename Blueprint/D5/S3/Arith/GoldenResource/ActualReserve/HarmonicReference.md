# Finite Harmonic Reference

## Abstract

The inclusive harmonic prime-power reference has a finite maximum at every real scale x > 1.

Set lambda_x = 1/(x log x), v_p(x) = Nat.log p floor(x), Q_p(a) = sum from k = 1 to a of 1/(k p^k), and H_p(a) = Q_p(a) - lambda_x a log p. The primes in T_x are precisely the actual primes p <= x. P(x) sums Q_p(v_p), psi(x) sums v_p log p, and F(x) = P(x) - lambda_x psi(x). The cutoff theorem makes these the inclusive prime-power sums of original theory section 87.

**Theorem 1.1 (Inclusive cutoff).**

$$\forall x,p,k, x> 1\land Prime\left(p\right)\Rightarrow (k\le v\left(x, p\right)\iff p^{k}\le x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_cutoff_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural exponent k, prime p and real x > 1, k <= v_p(x) if and only if p^k <= x. The Nat.log Galois connection and floor equivalence give finiteness and preserve a prime power equal to the real endpoint.

**Theorem 1.2 (Exact gain sign).**

$$\forall x,p,k, x> 1\land Prime\left(p\right)\land k\ge 1\Rightarrow (0\le \frac{1}{kp^{k}}-lambda\left(x\right) \cdot log\left(p\right)\iff p^{k}\le x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_gain_nonneg_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k >= 1 the reference gain is nonnegative exactly when p^k <= x. Positive denominators transform this into p^k log(p^k) <= x log x. Mathlib's strict monotonicity of t log t supplies the equivalence. At p^k = x the gain is zero, so either equality-layer choice preserves the value.

**Theorem 1.3 (Maximum against all exponents).**

$$\forall x,p,a, x> 1\land Prime\left(p\right)\Rightarrow H\left(x, p, a\right)\le H\left(x, p, v\left(x, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_objective_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a, including zero and a beyond the finite carrier, H_p(a) <= H_p(v_p). The objective increases through nonnegative gains and decreases after the cutoff. This is reference optimization; the existing actual marginal optimizer has a different objective.

**Theorem 1.4 (Actual prefix dominated by the reference maximum).**

$$\forall x,p,a, x> 1\land Prime\left(p\right)\Rightarrow u\left(x, p, a\right)\le H\left(x, p, v\left(x, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.actual_local_le_reference_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix compares the whole geometric prefix to the harmonic prefix. Exponent zero has both values zero. Subtracting the same cost and using the preceding maximum yields u_p(a) <= H_p(v_p). No comparison of individual actual and reference marginals is used.

**Theorem 1.5 (Exact sum on any finite actual-prime superset).**

$$\forall x,U, x> 1\land ActualPrimeSuperset\left(U, T\left(x\right)\right)\Rightarrow F\left(x\right)=\sum_{p\in U} H\left(x, p, v\left(x, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_pressure_sum_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite set U of actual primes containing T_x, F(x) is the sum of H_p(v_p) over U. A prime outside T_x has v_p = 0 and contributes zero. ActualReservePrimeMask uses U = T_x union n.primeFactors, so primes of the actual integer beyond the reference cutoff are retained in the complement.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.actual_local_le_reference_maximum`
- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_cutoff_spec`
- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_gain_nonneg_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_objective_maximal`
- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference.reference_pressure_sum_on`
- Dependency: [D5/S3/Arith/GoldenLocalThreshold](../../GoldenLocalThreshold.md)
- Dependency: [D5/S3/Arith/GoldenResource/PrefixDeficitKernel](../PrefixDeficitKernel.md)
- Dependency: [D5/S3/Arith/GoldenResource/ReferencePrefixDominance](../ReferencePrefixDominance.md)
