# Stephan's Complement-Reversal Recurrences

## Abstract

Stephan's binary complement-reversal recurrences and digit-count identities hold for all positive inputs.

All scalar values and the variables n and d are natural numbers; N denotes their domain. Subtraction is natural subtraction, truncated at zero. The operator digits_2(n) is Nat.digits 2 n: the little-endian binary digit list, empty at zero. The operator ofDigits_2 evaluates a list in base two with its first entry least significant. The operator dropLast removes the last entry, reverse reverses a list, map(f,L) applies f entrywise to L, append concatenates two lists, and [1] is the singleton list. The expression d : N mapped to 1-d denotes the digit-complement function. The operator count(c,L) counts entries equal to c in L. The operator log_2(n) is Nat.log 2 n, the floor of the base-two logarithm for positive n. Addition, multiplication and powers are natural-number operations. The functions a and complementRest are defined below; on positive inputs they represent A059894 and A054429. A000120 counts one bits, and A023416 counts zero bits in the canonical binary expansion of a positive number.

**Definition 1.1 (Complement and reverse the lower bits).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \left(\operatorname{ofDigits}_{2}\right)\left(\operatorname{append}\left(\operatorname{map}\left((d: \mathbb{N} \mapsto 1 - d), \operatorname{reverse}\left(\operatorname{dropLast}\left(\left(\operatorname{digits}_{2}\right)\left(n\right)\right)\right)\right), [1]\right)\right)$$

*Formalization.* `D5/S1/Digit/StephanComplementReverseRecurrence.a` (`✓ std3`).

*Citation.* Marc LeBrun; Ralf Stephan (2003). *OEIS A059894, complement and reverse all but the most significant bit*. URL: <https://oeis.org/A059894>.

*Commentary.*

Remove the most significant bit, reverse and complement the remaining bits, then append the most significant bit one. The definition is total on the naturals; the recurrence and counting clauses below quantify over positive inputs.

**Definition 1.2 (Complement the lower bits without reversal).**

$$\forall n: \mathbb{N}, \operatorname{complementRest}\left(n\right) = \left(\operatorname{ofDigits}_{2}\right)\left(\operatorname{append}\left(\operatorname{map}\left((d: \mathbb{N} \mapsto 1 - d), \operatorname{dropLast}\left(\left(\operatorname{digits}_{2}\right)\left(n\right)\right)\right), [1]\right)\right)$$

*Formalization.* `D5/S1/Digit/StephanComplementReverseRecurrence.complementRest` (`✓ std3`).

*Citation.* Marc LeBrun; Ralf Stephan (2003). *OEIS A059894, complement and reverse all but the most significant bit*. URL: <https://oeis.org/A059894>.

*Commentary.*

This transformation complements every bit except the most significant one and preserves the order of the lower bits.

**Theorem 1.3 (The A059894 recurrence and digit-count conjectures).**

$$(\operatorname{a}\left(1\right) = 1) \land ((\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(2 \cdot n\right) = \operatorname{a}\left(n\right) + 2^{\left(\operatorname{log}_{2}\right)\left(n\right) + 1})) \land ((\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left(2 \cdot n + 1\right) = \operatorname{a}\left(n\right) + 2^{\left(\operatorname{log}_{2}\right)\left(n\right)})) \land (\forall n: \mathbb{N}, (0 < n) \implies ((\operatorname{count}\left(1, \left(\operatorname{digits}_{2}\right)\left(\operatorname{a}\left(n\right)\right)\right) = \operatorname{count}\left(1, \left(\operatorname{digits}_{2}\right)\left(\operatorname{complementRest}\left(n\right)\right)\right)) \land (\operatorname{count}\left(1, \left(\operatorname{digits}_{2}\right)\left(\operatorname{a}\left(n\right)\right)\right) = \operatorname{count}\left(0, \left(\operatorname{digits}_{2}\right)\left(n\right)\right) + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/StephanComplementReverseRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a059894-stephan-complement-reverse-recurrence` (proved) by `D5/S1/Digit/StephanComplementReverseRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a059894-stephan-complement-reverse-recurrence","declaration_gid":"D5/S1/Digit/StephanComplementReverseRecurrence.result","resolution_kind":"proved"} -->

*Citation.* Marc LeBrun; Ralf Stephan (2003). *OEIS A059894, complement and reverse all but the most significant bit*. URL: <https://oeis.org/A059894>.

*Commentary.*

The entry cited in stephan2003a059894 attributes both conjectures to Ralf Stephan. The binary digit lemmas for twice n and twice n plus one, together with positional evaluation and digit-list length, give the two recurrences. Reconstructing the transformed digit lists shows that reversal preserves the one count and complementation turns the original zero count into the one count below the retained leading one.

## References

- Truth anchor: `D5/S1/Digit/StephanComplementReverseRecurrence.a`
- Truth anchor: `D5/S1/Digit/StephanComplementReverseRecurrence.complementRest`
- Truth anchor: `D5/S1/Digit/StephanComplementReverseRecurrence.result`
