# Layman's OEIS A196226 Divisor-Power Congruence Conjectures

## Abstract

The integer 690 refutes John W. Layman's three divisor-power congruence conjectures.

**Definition 1.1 (Membership in OEIS A196226).**

$$\forall m \in \mathrm{Nat},\; (\operatorname{membership}\left(m\right)) \Leftrightarrow ((2 \mid m) \land (ArithmeticFunction.sigma\left(1, m\right) \bmod m = 3 + (m / 2)))$$

*Formalization.* `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.membership` (`✓ std3`).

*Citation.* John W. Layman (2011). *OEIS A196226, divisor-sum residue and divisor-power congruence conjectures*. URL: <https://oeis.org/A196226>.

*Commentary.*

A natural number m is a member when it is even and the remainder of sigma sub one of m modulo m equals 3 + m/2. Here slash denotes natural-number integer division; the divisibility clause makes m/2 exact.

**Definition 1.2 (Layman's three congruence conjectures).**

$$(claim) \Leftrightarrow ((\forall m \in \mathrm{Nat},\; ((\operatorname{membership}\left(m\right)) \land (14 \le m)) \Rightarrow (Nat.ModEq\left(m, ArithmeticFunction.sigma\left(2, m\right), 5 + (m / 2)\right))) \lor \left((\forall m \in \mathrm{Nat},\; ((\operatorname{membership}\left(m\right)) \land (22 \le m)) \Rightarrow (Nat.ModEq\left(m, ArithmeticFunction.sigma\left(3, m\right), 9 + (m / 2)\right))) \lor (\forall m \in \mathrm{Nat},\; ((\operatorname{membership}\left(m\right)) \land (38 \le m)) \Rightarrow (Nat.ModEq\left(m, ArithmeticFunction.sigma\left(4, m\right), 17 + (m / 2)\right)))\right))$$

*Formalization.* `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim` (`✓ std3`).

*Citation.* John W. Layman (2011). *OEIS A196226, divisor-sum residue and divisor-power congruence conjectures*. URL: <https://oeis.org/A196226>.

*Commentary.*

The claim is the disjunction of the three published universal congruences. Their thresholds are 14, 22, and 38; their divisor-power exponents are 2, 3, and 4; and their constants are 5, 9, and 17. Nat.ModEq(m,x,y) means that x and y are congruent modulo m, and every slash denotes natural-number integer division.

**Theorem 1.3 (All three conjectures are false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a196226-layman-divisor-power-congruence-refutation` (refuted) by `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a196226-layman-divisor-power-congruence-refutation","declaration_gid":"D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* John W. Layman (2011). *OEIS A196226, divisor-sum residue and divisor-power congruence conjectures*. URL: <https://oeis.org/A196226>.

*Commentary.*

At m = 690, sigma sub one is 1728, so the membership remainder is 348. The next three divisor-power sums are 689000, 386358336, and 244202442248. Their remainders modulo 690 are 380, 426, and 668, rather than the required 350, 354, and 362. Thus each disjunct fails.

## References

- Truth anchor: `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.claim`
- Truth anchor: `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.membership`
- Truth anchor: `D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.result`
