# Square Divisibility of Odd Central Stirling Numbers

## Abstract

Every odd column of the central Stirling numbers is divisible by the square of that column.

**Definition 1.1 (Bala's assertion).**

$$\operatorname{claim} \iff \forall n: \mathbb{N}, (2 \cdot n + 1)^{2} \mid \operatorname{Nat}.\operatorname{stirlingSecond}\left(2 \cdot (2 \cdot n + 1), (2 \cdot n + 1)\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.claim` (`✓ std3`).

*Citation.* Peter Bala (2025). *OEIS A007820 COMMENTS conjecture on square divisibility of odd central Stirling numbers*. URL: <https://oeis.org/A007820>.

*Commentary.*

OEIS A007820, COMMENTS (unnumbered web entry), states verbatim: "%C Conjecture: a(2*n+1) is divisible by (2*n + 1)^2. - _Peter Bala_, Mar 30 2025" Its NAME is "%N Stirling numbers of second kind S(2n,n)." Here n ranges over all natural numbers, including zero. Nat.stirlingSecond r k counts partitions of an r-element labelled set into exactly k nonempty, unlabelled blocks. The column is 2*n+1 and the row is twice that column; divisibility is in the natural numbers.

**Theorem 1.2 (The assertion holds).**

$$\forall n: \mathbb{N}, (2 \cdot n + 1)^{2} \mid \operatorname{Nat}.\operatorname{stirlingSecond}\left(2 \cdot (2 \cdot n + 1), (2 \cdot n + 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala-a007820` (proved) by `D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala-a007820","declaration_gid":"D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2025). *OEIS A007820 COMMENTS conjecture on square divisibility of odd central Stirling numbers*. URL: <https://oeis.org/A007820>.

*Commentary.*

Integer inclusion-exclusion expresses the factorial-weighted Stirling number as an alternating binomial sum. Reflecting its index and expanding by the binomial theorem gives a reflection identity for every natural column m, including zero. For odd m its zero-order term is the negative of the central Stirling number. The first-order term contains 2*m^2, and each higher-order term contains m^2. Thus m^2 divides twice the central Stirling number. Since m^2 is coprime to two, it divides the number itself. Setting m=2*n+1 proves the assertion, including n=0 and all odd composite columns.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.claim`
- Truth anchor: `D5/S1/Recurrence/Parity/CentralStirlingOddSquareDivisibility.result`
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](StirlingPowerFactorialPrimePeriod.md)
