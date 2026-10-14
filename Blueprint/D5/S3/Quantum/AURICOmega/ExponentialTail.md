# Exponential remainder

## Abstract

A geometric estimate for the analytic exponential remainder in a complete normed real algebra.

**Theorem 1.1 (A bound from successive factorial ratios).**

$$\forall B \in \operatorname{Type}\left(\right),\; [\operatorname{NormedRing}\left(B\right)] [\operatorname{NormedAlgebra}\left(\mathbb{R}, B\right)] [\operatorname{CompleteSpace}\left(B\right)] [\operatorname{NormOneClass}\left(B\right)] \forall x \in B, r \in \mathbb{R}, n \in \mathbb{N},\; \left(0 \le r \land \left(\operatorname{norm}\left(x\right) \le r \land r < n + 1\right)\right) \Rightarrow \operatorname{norm}\left(\operatorname{exponentialRemainder}\left(x, n\right)\right) \le \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{power}\left(r, n\right), \operatorname{factorial}\left(n\right)\right), \operatorname{subtract}\left(1, \operatorname{divide}\left(r, n + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write exponentialRemainder(x,n)=exp(x)-sum from k=0 to n-1 of x^k/k!. Let B be a complete normed real algebra with a submultiplicative norm and norm of the identity equal to one. For a nonnegative r with norm(x) at most r, and r<n+1, the omitted terms of the exponential series have norms bounded by r^n/n! times (r/(n+1))^k. Summing this geometric majorant gives the displayed bound.

Mathlib supplies convergence of the exponential power series, the comparison theorem for sums in normed groups, and the sum of the geometric series. The factorial coefficient estimate joins these results without commuting products. For matrices, the induced maximum row-sum norm is submultiplicative and fits these assumptions; the entrywise maximum norm does not supply that multiplication estimate.

At r=2 and n=13 the ratio is 1/7, so the bound is (7/6) times 2^13/13!. The estimate concerns the actual exponential, rather than only a finite polynomial.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le`
