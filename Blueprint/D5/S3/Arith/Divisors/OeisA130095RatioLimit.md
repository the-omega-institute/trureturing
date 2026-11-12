# The OEIS A130095 ratio conjecture

## Abstract

The complete successive-term ratio limit in OEIS A130095.

**Definition 1.1 (The odd-Fibonacci divisor transform).**

$$\forall n \in Nat,\; \operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{divisors}\left(n\right), (fun d \mapsto \operatorname{Nat}.\operatorname{fib}\left(2 \cdot d - 1\right))\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA130095RatioLimit.a` (`✓ std3`).

*Citation.* Gary W. Adamson; Peter Bala (2007). *OEIS A130095: Inverse Möbius transform of odd-indexed Fibonacci numbers*. URL: <https://oeis.org/A130095>.

*Commentary.*

Peter Bala's formula in OEIS A130095 is a(n) = sum {d | n} Fibonacci(2*d - 1). Nat.fib has F(0)=0 and F(1)=1. For positive n, Nat.divisors contains every positive divisor, including n. The extension a(0)=0 is an empty sum and does not enter the eventual ratio.

**Theorem 1.2 (The complete eventual ratio tends to the squared golden ratio).**

$$\forall epsilon \in Real,\; 0 < epsilon \Rightarrow \left(\exists N \in Nat,\; 2 \le N \land \left(\forall n \in Nat,\; N \le n \Rightarrow \left|\frac{(\operatorname{a}\left(n\right):Real)}{(\operatorname{a}\left(n - 1\right):Real)} - \frac{1 + \sqrt{5}}{2}^{2}\right| < epsilon\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA130095RatioLimit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gary W. Adamson; Peter Bala (2007). *OEIS A130095: Inverse Möbius transform of odd-indexed Fibonacci numbers*. URL: <https://oeis.org/A130095>.

*Commentary.*

The source comment states: “Conjecture: a(n)/a(n-1) tends to phi^2.” Here phi is (1+sqrt(5))/2. Every positive real epsilon has a natural threshold N at least two, and the estimate holds for every natural n at least N. Both sequence values are cast to Real before division. Subtraction in the sequence argument n-1 is natural subtraction. There is no subsequence restriction or additional arithmetic hypothesis.

Split a(n) as F(2n-1)+R(n), where R sums the proper divisors. A positive proper divisor d satisfies 2d<=n. The telescoping Fibonacci sum bounds R(n) by F(n). The doubling identity gives F(n)^2<=F(2n-1), so R(n)/F(2n-1)<=1/F(n), which tends to zero. Two instances of Mathlib's adjacent Fibonacci ratio theorem give F(2n-1)/F(2n-3) tending to phi^2. Multiplying by the quotient of the two relative correction factors proves the displayed full limit. The proof establishes a(n)>0 for every n>=1 and discharges every denominator obligation used in the transfer.

This delivery uses the external named open-problem-resolution route preregistered in issue 29484. The proof steps are classified bind-only under the repository rule; no separate new general theorem or priority claim is asserted. Independent review and canonical freeze remain separate requirements. The source note records the bounded literature qualification.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA130095RatioLimit.a`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA130095RatioLimit.result`
