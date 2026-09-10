# A Counterexample to Pure Periodicity of the Secant Numbers

## Abstract

The Euler secant numbers refute pure periodicity with period dividing phi(27).

The comment recorded in bala2023a000364 conjectures pure periodicity of the sequence starting at index 1, with period dividing phi(k), for every integer modulus k. Here k is 27. The symbols a and b denote the integer sequence and its independently defined recurrence in ZMod(27). The function red denotes the canonical map from the integers to ZMod(27), choose denotes the natural binomial coefficient, and phi denotes Euler's totient. All indices are natural numbers; subtraction in an index is natural subtraction. The sum over j in Fin(n+1) uses the natural value of j in every summand. Numerals, signs, products and sums in each recurrence are interpreted in the codomain of that sequence.

**Definition 1.1 (The integer secant recurrence).**

$$\begin{aligned}a: \mathbb{N} \to \mathbb{Z}\\(\operatorname{a}(0) = 1) \land (\forall n: \mathbb{N}, (\operatorname{a}(n + 1) = \sum_{j \in \operatorname{Fin}(n + 1)} ((((-1)^{j + 2}) \cdot (\operatorname{choose}((2) \cdot (n + 1), (2) \cdot (j + 1)))) \cdot (\operatorname{a}(n - j)))))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer sequence a has constant value a(0)=1 and obeys the recurrence in bala2023a000364 with its summation index shifted by one.

**Definition 1.2 (The recurrence modulo 27).**

$$\begin{aligned}b: \mathbb{N} \to \operatorname{ZMod}(27)\\(\operatorname{b}(0) = 1) \land (\forall n: \mathbb{N}, (\operatorname{b}(n + 1) = \sum_{j \in \operatorname{Fin}(n + 1)} ((((-1)^{j + 2}) \cdot (\operatorname{choose}((2) \cdot (n + 1), (2) \cdot (j + 1)))) \cdot (\operatorname{b}(n - j)))))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence b is defined by the same recurrence directly in ZMod(27).

**Theorem 1.3 (The defining recurrence holds).**

$$(\operatorname{a}(0) = 1) \land (\forall n: \mathbb{N}, (\operatorname{a}(n + 1) = \sum_{j \in \operatorname{Fin}(n + 1)} ((((-1)^{j + 2}) \cdot (\operatorname{choose}((2) \cdot (n + 1), (2) \cdot (j + 1)))) \cdot (\operatorname{a}(n - j)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding a gives both the initial condition and the recurrence.

**Theorem 1.4 (The recurrence determines a uniquely).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, ((\operatorname{c}(0) = 1) \implies ((\forall n: \mathbb{N}, (\operatorname{c}(n + 1) = \sum_{j \in \operatorname{Fin}(n + 1)} ((((-1)^{j + 2}) \cdot (\operatorname{choose}((2) \cdot (n + 1), (2) \cdot (j + 1)))) \cdot (\operatorname{c}(n - j))))) \implies (c = a)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction compares c and a at every index. Each term on the right uses a strictly smaller index, so equality propagates to the next coefficient.

**Theorem 1.5 (Agreement with the initial published values).**

$$(\operatorname{a}(0) = 1) \land ((\operatorname{a}(1) = 1) \land ((\operatorname{a}(2) = 5) \land (\operatorname{a}(3) = 61)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.initial_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defining integer recurrence gives the first four DATA values in bala2023a000364.

**Theorem 1.6 (Reduction commutes with the recurrence).**

$$\forall n: \mathbb{N}, (\operatorname{red}(\operatorname{a}(n)) = \operatorname{b}(n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction moves the integer cast through the finite sum, powers and products, then identifies every smaller coefficient with b.

**Theorem 1.7 (The first positive coefficient modulo 27).**

$$\operatorname{red}(\operatorname{a}(1)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.residue_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction of the first positive coefficient gives 1 in ZMod(27).

**Theorem 1.8 (The nineteenth coefficient modulo 27).**

$$\operatorname{red}(\operatorname{a}(19)) = 10$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.residue_nineteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successive evaluations of the reduced recurrence give b(19)=10. The reduction theorem transfers this certificate to a.

**Definition 1.9 (The conjecture at modulus 27).**

$$\operatorname{balaConjecture}() \iff (\exists d: \mathbb{N}, ((0 < d) \land ((d \mid \operatorname{phi}(27)) \land (\forall n: \mathbb{N}, ((1 \le n) \implies (\operatorname{red}(\operatorname{a}(n + d)) = \operatorname{red}(\operatorname{a}(n))))))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.balaConjecture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposition balaConjecture says that the sequence from index 1 has a positive period d dividing phi(27).

**Theorem 1.10 (Pure periodicity fails at modulus 27).**

$$\neg (\operatorname{balaConjecture}())$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.bala_conjecture_false` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a000364-secant-number-pure-period-refutation` (refuted) by `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.bala_conjecture_false`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a000364-secant-number-pure-period-refutation","declaration_gid":"D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.bala_conjecture_false","resolution_kind":"refuted"} -->

*Citation.* Peter Bala (2023). *OEIS A000364, Euler (secant) numbers*. URL: <https://oeis.org/A000364>.

*Commentary.*

Any period d dividing phi(27)=18 would make 18 a period, by the theorem that a natural multiple of a period is a period. This would equate red(a(1))=1 with red(a(19))=10 in ZMod(27), a contradiction. This refutes the word purely in the conjecture; it makes no claim about eventual periodicity or about the stated odd-prime theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a_recurrence`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.a_unique`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.b`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.balaConjecture`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.bala_conjecture_false`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.initial_values`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.reduction`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.residue_nineteen`
- Truth anchor: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.residue_one`
