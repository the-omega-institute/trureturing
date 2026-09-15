# The OEIS A103585 Sloping-Binary Period Conjecture

## Abstract

The 129th and 172nd entries refute the proposed period 43 of OEIS A103585.

**Definition 1.1 (The sloping-binary sequence).**

$$\forall k \in \mathrm{Nat},\; \operatorname{s}\left(k\right) = k + \sum_{m \in \operatorname{Icc}\left(1, k + 1\right)} (\operatorname{ite}\left(\left(k + m\right) \bmod 2^{m} = 0, 2^{m}, 0\right))$$

*Formalization.* `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.s` (`✓ std3`).

*Citation.* Benoit Cloitre; Philippe Deléham; Ralf Stephan (2005). *OEIS A103585, numbers k with (A102370(k)-k)/2 = 1, read mod 4*. URL: <https://oeis.org/A103585>.

*Commentary.*

The value s(k) is A102370(k), written as the finite conditional sum in its OEIS formula.

**Definition 1.2 (The A103585 selection predicate).**

$$\forall k \in \mathrm{Nat},\; (\operatorname{P}\left(k\right)) \Leftrightarrow (\operatorname{s}\left(k\right) = k + 2)$$

*Formalization.* `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.P` (`✓ std3`).

*Citation.* Benoit Cloitre; Philippe Deléham; Ralf Stephan (2005). *OEIS A103585, numbers k with (A102370(k)-k)/2 = 1, read mod 4*. URL: <https://oeis.org/A103585>.

*Commentary.*

The predicate P selects exactly those natural k for which s(k) equals k+2.

**Definition 1.3 (The zero-based A103585 sequence).**

$$\forall i \in \mathrm{Nat},\; \operatorname{A}\left(i\right) = \operatorname{nth}\left(P, i\right) \bmod 4$$

*Formalization.* `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.A` (`✓ std3`).

*Citation.* Benoit Cloitre; Philippe Deléham; Ralf Stephan (2005). *OEIS A103585, numbers k with (A102370(k)-k)/2 = 1, read mod 4*. URL: <https://oeis.org/A103585>.

*Commentary.*

The value A(i) is the i-th natural satisfying P, reduced modulo four. Thus OEIS a(m) equals A(m-1).

**Definition 1.4 (Stephan's period-43 claim).**

$$(claim) \Leftrightarrow (\forall i \in \mathrm{Nat},\; \operatorname{A}\left(i + 43\right) = \operatorname{A}\left(i\right))$$

*Formalization.* `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.claim` (`✓ std3`).

*Citation.* Benoit Cloitre; Philippe Deléham; Ralf Stephan (2005). *OEIS A103585, numbers k with (A102370(k)-k)/2 = 1, read mod 4*. URL: <https://oeis.org/A103585>.

*Commentary.*

The claim asserts that shifting any zero-based index by 43 preserves A.

**Theorem 1.5 (The period-43 claim fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a103585-sloping-binary-period-refutation` (refuted) by `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a103585-sloping-binary-period-refutation","declaration_gid":"D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benoit Cloitre; Philippe Deléham; Ralf Stephan (2005). *OEIS A103585, numbers k with (A102370(k)-k)/2 = 1, read mod 4*. URL: <https://oeis.org/A103585>.

*Commentary.*

The finite ranking certificate identifies the 129th entry with 383 modulo four and the 172nd entry with 513 modulo four. Hence a(129)=3 differs from a(172)=1. This refutes the period-43 claim without changing the definition of A102370 or asserting a true period.

## References

- Truth anchor: `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.A`
- Truth anchor: `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.P`
- Truth anchor: `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.claim`
- Truth anchor: `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.result`
- Truth anchor: `D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.s`
