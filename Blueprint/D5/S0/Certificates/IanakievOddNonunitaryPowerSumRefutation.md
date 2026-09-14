# The OEIS A319927 Odd Non-Unitary Power-Sum Conjecture

## Abstract

The sequence member 9216 refutes Ianakiev's power-sum divisibility conjecture.

**Definition 1.1 (Non-unitary divisors).**

$$\forall n \in \mathrm{Nat},\; \operatorname{nonunitaryDivisors}\left(n\right) = \{d \in \operatorname{divisors}\left(n\right) \mid 1 < \operatorname{gcd}\left(d, n / d\right)\}$$

*Formalization.* `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.nonunitaryDivisors` (`✓ std3`).

*Citation.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

The divisors d of n are filtered by gcd(d,n/d)>1. The slash denotes natural-number integer division; it is exact because every d in the displayed domain divides n.

**Definition 1.2 (All non-unitary divisor powers).**

$$\forall k \in \mathrm{Nat}, n \in \mathrm{Nat},\; \operatorname{S}\left(k, n\right) = \sum_{d \in \operatorname{nonunitaryDivisors}\left(n\right)} (d^{k})$$

*Formalization.* `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.S` (`✓ std3`).

*Citation.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

For natural k and n, S(k,n) sums d^k over all non-unitary divisors d of n.

**Definition 1.3 (Odd non-unitary divisor powers).**

$$\forall k \in \mathrm{Nat}, n \in \mathrm{Nat},\; \operatorname{O}\left(k, n\right) = \sum_{d \in \{d \in \operatorname{nonunitaryDivisors}\left(n\right) \mid d \bmod 2 = 1\}} (d^{k})$$

*Formalization.* `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.O` (`✓ std3`).

*Citation.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

For natural k and n, O(k,n) restricts the same sum to divisors with remainder one modulo two.

**Definition 1.4 (Membership in A319927).**

$$\forall n \in \mathrm{Nat},\; (\operatorname{member}\left(n\right)) \Leftrightarrow ((0 < n) \land \left((0 < \operatorname{O}\left(2, n\right)) \land (\operatorname{O}\left(2, n\right) \mid \operatorname{S}\left(2, n\right))\right))$$

*Formalization.* `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.member` (`✓ std3`).

*Citation.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

A positive natural n is a member when O(2,n) is nonzero and divides S(2,n). The nonzero condition follows the PARI isok guard.

**Definition 1.5 (Ianakiev's conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (\operatorname{member}\left(n\right)) \Rightarrow (\forall k \in \mathrm{Nat},\; \operatorname{O}\left(k, n\right) \mid \operatorname{S}\left(k, n\right)))$$

*Formalization.* `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.claim` (`✓ std3`).

*Citation.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

For every member n and every natural power k, the conjecture asserts that O(k,n) divides S(k,n).

**Theorem 1.6 (The conjecture fails at 9216).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a319927-odd-nonunitary-power-sum-refutation` (refuted) by `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a319927-odd-nonunitary-power-sum-refutation","declaration_gid":"D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan N. Ianakiev (2018). *OEIS A319927, Numbers k such that the sum of the squares of the odd non-unitary divisors of k divides the sum of the squares of the non-unitary divisors of k*. URL: <https://oeis.org/A319927>.

*Commentary.*

At 9216=2^10*3^2 the odd non-unitary divisor set is {3}; O(1,9216)=3 and S(1,9216)=16361, so the claimed divisibility fails. Munn's 2020 question about p=3 and the entry's 2022 remark are not claimed here.

## References

- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.O`
- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.S`
- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.claim`
- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.member`
- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.nonunitaryDivisors`
- Truth anchor: `D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.result`
