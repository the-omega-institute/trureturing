# The A328959 Divisor-Count Bound

## Abstract

The divisor-count expression in OEIS A328959 is nonnegative from n=2 onward.

**Definition 1.1 (The integer-valued sequence).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = sigmaZero\left(n\right) - 2 - (\left(cardFactors\left(n\right) - 1\right) \cdot cardDistinctFactors\left(n\right))$$

*Formalization.* `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.a` (`✓ std3`).

*Citation.* Gus Wiseman (2019). *OEIS A328959, a(n) = sigma_0(n) - 2 - (omega(n) - 1) * nu(n)*. URL: <https://oeis.org/A328959>.

*Commentary.*

The formula is a(n) = sigma_0(n) - 2 - (Omega(n) - 1) times omega(n). Here sigma_0 is the number of divisors (A000005), Omega is the number of prime factors with multiplicity (the entry's omega, A001222), and omega is the number of distinct prime factors (the entry's nu, A001221). The values are integers. The source's exceptional value is a(1)=-1.

**Theorem 1.2 (Nonnegativity from two onward).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow 0 \le a\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.wiseman_a328959` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a328959-divisor-count-prime-factor-bound` (proved) by `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.wiseman_a328959`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a328959-divisor-count-prime-factor-bound","declaration_gid":"D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.wiseman_a328959","resolution_kind":"proved"} -->

*Citation.* Gus Wiseman (2019). *OEIS A328959, a(n) = sigma_0(n) - 2 - (omega(n) - 1) * nu(n)*. URL: <https://oeis.org/A328959>.

*Commentary.*

For n at least two, write each positive prime exponent as one plus b. The product of the factors two plus b dominates its constant and linear parts. Two inductive power estimates then bound the distinct prime count and its quadratic term, proving that a(n) is nonnegative.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.a`
- Truth anchor: `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.wiseman_a328959`
