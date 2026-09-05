# Even-Length Barker Sequences and the Mod-Four Boundary Obstruction

## Abstract

A boundary autocorrelation congruence gives the classical divisibility-by-four obstruction for even Barker sequences, together with explicit finite witnesses.

**Definition 1.1 (Aperiodic correlation on a finite prefix).**

Lean statement: `D5/S1/Words/BarkerEvenLengthModFourObstruction.aperiodicCorrelation`

*Formalization.* `D5/S1/Words/BarkerEvenLengthModFourObstruction.aperiodicCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a sequence a and natural numbers n and k, the kth aperiodic correlation is the sum of a(i)a(i+k) over 0 <= i < n-k.

**Definition 1.2 (The Barker condition on a finite prefix).**

Lean statement: `D5/S1/Words/BarkerEvenLengthModFourObstruction.IsBarker`

*Formalization.* `D5/S1/Words/BarkerEvenLengthModFourObstruction.IsBarker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first n entries must all be signs, and every nonzero shift below n must have aperiodic correlation of absolute value at most one.

**Theorem 1.3 (Parity and mod-four boundary congruences).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, (\forall i: \mathbb{N}, i < n \implies (a(i) = 1 \lor a(i) = -1)) \implies ((\forall k: \mathbb{N}, k \le n \implies \operatorname{aperiodicCorrelation}(a, n, k) \equiv n - k (\operatorname{mod} 2)) \land (2 \le n \implies \operatorname{aperiodicCorrelation}(a, n, 2) + \operatorname{aperiodicCorrelation}(a, n, n - 2) \equiv n (\operatorname{mod} 4))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker_correlation_congruences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every sign product is congruent to one modulo two, proving the first conjunct for every shift. For the second conjunct, the pointwise identity xy = x-y+1 modulo four telescopes at stride two and leaves exactly the two boundary correlations.

**Theorem 1.4 (Even Barker lengths above two are divisible by four).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, (\operatorname{Even}(n) \land 2 < n) \implies ((\operatorname{IsBarker}(a, n) \implies n \bmod 4 = 0) \land (n \bmod 4 = 2 \implies \neg \operatorname{IsBarker}(a, n))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BarkerEvenLengthModFourObstruction.even_barker_length_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive even shifts the parity congruence and Barker bound force the correlation to vanish. Applying this at shifts two and n-2 in the mod-four boundary congruence proves divisibility by four. The second conjunct records the resulting exclusion of every length congruent to two modulo four.

**Theorem 1.5 (The modulo-four-two exclusion as a named companion).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, (\operatorname{Even}(n) \land 2 < n \land n \bmod 4 = 2) \implies \neg \operatorname{IsBarker}(a, n).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BarkerEvenLengthModFourObstruction.no_even_barker_of_mod_four_eq_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exclusion is exposed as an addressable bind-only companion of the divisibility theorem, with exactly the hypotheses named in the preregistered remark.

**Definition 1.6 (The length-thirteen Barker word).**

Lean statement: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker13`

*Formalization.* `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function has positive entries at indices 0, 1, 2, 3, 4, 7, 8, 10, and 12 and negative entries elsewhere, so its first thirteen signs are +++++--++-+-+.

**Definition 1.7 (The length-four Barker word).**

Lean statement: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker4`

*Formalization.* `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function is positive at indices 0, 1, and 2 and negative elsewhere, so its first four signs are +++-.

**Definition 1.8 (A length-eight equal-correlation non-Barker word).**

Lean statement: `D5/S1/Words/BarkerEvenLengthModFourObstruction.oddEqualEight`

*Formalization.* `D5/S1/Words/BarkerEvenLengthModFourObstruction.oddEqualEight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function is negative only at index 6, so its first eight signs are ++++++-+.

**Theorem 1.9 (Finite witnesses for Barker and equal-correlation behavior).**

$$\operatorname{IsBarker}(barker_{13}, 13) \land \operatorname{IsBarker}(barker_{4}, 4) \land (\operatorname{aperiodicCorrelation}(oddEqualEight, 8, 1) = 3 \land \operatorname{aperiodicCorrelation}(oddEqualEight, 8, 3) = 3 \land \neg \operatorname{IsBarker}(oddEqualEight, 8)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker_obstruction_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel enumeration verifies all nontrivial correlations for the classical length-thirteen and length-four Barker words. It also computes the first and third correlations of ++++++-+ as three and verifies that this length-eight word is not Barker, without using native_decide.

## References

- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.IsBarker`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.aperiodicCorrelation`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker13`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker4`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker_correlation_congruences`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.barker_obstruction_witnesses`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.even_barker_length_mod_four`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.no_even_barker_of_mod_four_eq_two`
- Truth anchor: `D5/S1/Words/BarkerEvenLengthModFourObstruction.oddEqualEight`
