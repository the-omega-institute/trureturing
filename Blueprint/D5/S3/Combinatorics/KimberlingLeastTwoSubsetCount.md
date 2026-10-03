# Kimberling's least-two-element subset count

## Abstract

The least-two-element subset count agrees with OEIS A077866 after shifting the index by three.

For a subset of {1,...,N}, let b(N) count those with two least elements a<b and maximum a+b. Positivity makes the source's more-than-one-element condition automatic. The sequence A is defined independently by A(0)=1, A(1)=2, A(2)=5, A(3)=8 and A(n+4)+4 A(n+1)=2 A(n+3)+A(n+2)+2 A(n).

**Theorem 1.1 (All-index subset interpretation of A077866).**

$$\left(b\left(0\right) = 0 \land \left(b\left(1\right) = 0 \land b\left(2\right) = 0\right)\right) \land \left(\forall n \in \mathbb{N},\; b\left(n + 3\right) = A\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a077866-least-two-subset-count` (proved) by `D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a077866-least-two-subset-count","declaration_gid":"D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2022). *OEIS A077866: Expansion of (1-x)^(-1)/(1-x-2*x^2+2*x^3)*. URL: <https://oeis.org/A077866>.

*Commentary.*

Every counted subset uniquely has the form {a,b,a+b} union T, where 0<a<b, a+b<=N, and T is any subset of (b,a+b). The resulting weighted sum is evaluated at odd and even indices and matched to the independently defined OEIS recurrence. The three empty-range base cases are explicit.

## References

- Truth anchor: `D5/S3/Combinatorics/KimberlingLeastTwoSubsetCount.result`
