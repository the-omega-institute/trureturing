# Large Concentrated Prime Descent

## Abstract

A concentrated pure prime at least 73 cannot occur under the terminal-donor period and minimality hypotheses.

**Theorem 1.1 (Large concentrated pure primes are impossible under terminal-donor hypotheses).**

Lean statement: `D5/S3/Arith/Covering/LargeConcentratedPrimeDescent.no_large_concentrated_pure_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/LargeConcentratedPrimeDescent.no_large_concentrated_pure_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a distinct odd covering system minimal first in class count and then in modulus sum. If F contains a pure prime class p with p at least 73, all its private points have one residue modulo 3, and every original modulus divides 9 * p^G * W with W coprime to 3p, then no such F exists.

The private projection modulo 9 has at most three values. The existing terminal-donor descent applies because 27 * 3 + 1 is at most p + 9, and its strict modulus-sum decrease contradicts count minimality or same-count sum minimality.

The result is conditional: it does not supply a pure prime, the period factorization, or the concentration hypothesis for an arbitrary cover.

## References

- Truth anchor: `D5/S3/Arith/Covering/LargeConcentratedPrimeDescent.no_large_concentrated_pure_prime`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/TerminalDonor](../Congruence/ConditionalComparison/TerminalDonor.md)
- Dependency: [D5/S3/Arith/Covering/ConcentratedPrimeSingleton](ConcentratedPrimeSingleton.md)
