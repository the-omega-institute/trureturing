# The OEIS A181278 Binary Gram-Row Recurrence

## Abstract

The n = 4 term refutes Barker's published recurrence for OEIS A181278.

**Definition 1.1 (The A181278 counting function).**

$$\forall n \in \mathrm{Nat},\; a181278\left(n\right) = countP\left((p \mapsto decide\left(fst\left(p\right) < snd\left(p\right) \land 2 \cdot (length\left(filter\left((i \mapsto testBit\left(fst\left(p\right), i\right)), range\left(n\right)\right)\right) \bmod 2) + (length\left(filter\left((i \mapsto (testBit\left(fst\left(p\right), i\right) \land testBit\left(snd\left(p\right), i\right))), range\left(n\right)\right)\right) \bmod 2) > 2 \cdot (length\left(filter\left((i \mapsto (testBit\left(fst\left(p\right), i\right) \land testBit\left(snd\left(p\right), i\right))), range\left(n\right)\right)\right) \bmod 2) + (length\left(filter\left((i \mapsto testBit\left(snd\left(p\right), i\right)), range\left(n\right)\right)\right) \bmod 2)\right)), product\left(range\left(2^{n}\right), range\left(2^{n}\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.a181278` (`✓ std3`).

*Citation.* Colin Barker (2018). *OEIS A181278, binary matrices with ordered rows and decreasing mod-2 Gram rows*. URL: <https://oeis.org/A181278>.

*Commentary.*

The range from zero through 2^n-1 lists every length-n binary row once, including rows with leading zeroes. The predicate countP counts ordered pairs p whose first row is smaller than the second. Parity is the remainder modulo two of the number of set bits below n, and dot is the corresponding common-set-bit count. The final strict inequality compares the two Gram rows lexicographically with their first entries as the high digits.

**Definition 1.2 (Barker's published recurrence).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; 4 \le n \Rightarrow a181278\left(n\right) + 16 \cdot a181278\left(n - 3\right) = 4 \cdot a181278\left(n - 1\right) + 4 \cdot a181278\left(n - 2\right))$$

*Formalization.* `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.claim` (`✓ std3`).

*Citation.* Colin Barker (2018). *OEIS A181278, binary matrices with ordered rows and decreasing mod-2 Gram rows*. URL: <https://oeis.org/A181278>.

*Commentary.*

The index is the OEIS index without a shift, so a181278(1)=0. The premise 4<=n is exactly the published condition n>3. Moving the negative term to the left gives an equality of natural numbers that is equivalent after casting to the integers and introduces no extra nonnegativity hypothesis. Each displayed index subtraction is natural subtraction; under the premise, all three indices are positive.

**Theorem 1.3 (The recurrence fails at n = 4).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a181278-barker-binary-gram-recurrence-refutation` (refuted) by `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a181278-barker-binary-gram-recurrence-refutation","declaration_gid":"D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker (2018). *OEIS A181278, binary matrices with ordered rows and decreasing mod-2 Gram rows*. URL: <https://oeis.org/A181278>.

*Commentary.*

The defining finite count gives a181278(1)=0, a181278(2)=3, a181278(3)=11, and a181278(4)=48. Specializing the claim at n=4 would therefore assert 48=4*11+4*3=56, which is false.

## References

- Truth anchor: `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.a181278`
- Truth anchor: `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.claim`
- Truth anchor: `D5/S1/Words/Patterns/BarkerBinaryGramRecurrenceRefutation.result`
