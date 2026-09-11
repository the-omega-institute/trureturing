# Binary Valuations of Truncated Schenker Sums

## Abstract

The odd-n, positive-k valuation formulas of OEIS A398189 hold outside its stated exception.

All indices and factorial quotients are natural numbers. The sum includes both endpoints, from zero through n-k. Odd n implies n is positive. The theorem explicitly assumes 1 <= k <= n. The original k=0 formula and the even-n branch are already proved background in Amdeberhan, Callan and Moll (2013), Section 2.

**Definition 1.1 (The truncated factorial sum).**

$$\forall n,k: \mathbb{N}, \operatorname{S}\left(n, k\right) = \sum_{j = 0}^{n - k} \frac{\operatorname{factorial}\left(n - k\right)}{\operatorname{factorial}\left(j\right)} \cdot n^{j}$$

*Formalization.* `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.S` (`✓ std3`).

*Citation.* Peter Luschny (2026). *OEIS A398189, binary valuations of generalized Schenker sums*. URL: <https://oeis.org/A398189>.

*Commentary.*

This is the defining integer sum of A398187. Its natural divisions are exact throughout the summation range, because j! divides (n-k)!.

**Theorem 1.2 (The two valuation branches for odd n and positive k).**

$$\forall n,k: \mathbb{N}, (\operatorname{Odd}\left(n\right) \land 1 \le k \land k \le n) \Rightarrow ((\operatorname{Odd}\left(k\right) \Rightarrow \operatorname{v2}\left(\operatorname{S}\left(n, k\right)\right) = 0) \land ((\operatorname{Even}\left(k\right) \land k \bmod 16 \ne 14) \Rightarrow \operatorname{v2}\left(\operatorname{S}\left(n, k\right)\right) = \operatorname{v2}\left(k + 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.odd_positive_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny (2026). *OEIS A398189, binary valuations of generalized Schenker sums*. URL: <https://oeis.org/A398189>.

*Commentary.*

For odd k the binary valuation is zero. For even k outside 14 modulo 16 it is the binary valuation of k+2. The proof first identifies the sum with H(0)=1 and H(m+1)=n^(m+1)+(m+1)H(m). Six recursive steps have a history coefficient divisible by 16. Odd powers have period four modulo 16, so this identity reduces every length at least six to residues. The shorter lengths are treated separately. The resulting residues are nonzero in the asserted range, so they determine the exact valuation. This proof is derived in the present Lean module; the OEIS comments state the formulas as conjectures. No formula is asserted for k congruent to 14 modulo 16.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.S`
- Truth anchor: `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.odd_positive_branches`
