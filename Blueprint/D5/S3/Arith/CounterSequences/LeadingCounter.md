# Exact multiplicities in the leading-digit counter sequence

## Abstract

Every positive integer occurs nine times in A384309, except 1 which occurs ten times.

**Theorem 1.1 (Initial term).**

$$\operatorname{a}\left(1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CounterSequences/LeadingCounter.a_one` (`✓ std3`). ∎

*Citation.* David James Sycamore (2025). *A384309 — the leading decimal digit counter sequence*. URL: <https://oeis.org/A384309>.

*Commentary.*

The sequence starts at position 1. The auxiliary value at position 0 is zero, so it contributes no occurrence of a positive integer.

**Theorem 1.2 (Count the current term before reading the next term).**

$$\forall t \in \mathbb{N}, 0 < t \implies \operatorname{a}\left(t+1\right) = \operatorname{counter}\left(\operatorname{leading10}\left(\operatorname{a}\left(t\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CounterSequences/LeadingCounter.a_recurrence` (`✓ std3`). ∎

*Citation.* David James Sycamore (2025). *A384309 — the leading decimal digit counter sequence*. URL: <https://oeis.org/A384309>.

*Commentary.*

Here counter(d,t) counts positions j from 1 through t with leading10(a(j))=d. The leading digit is the last element of Mathlib's little-endian decimal digit list. At each step exactly one of the nine counters increases by one, and its new value becomes the next term.

**Theorem 1.3 (Nine occurrences, with one extra initial 1).**

$$\forall k \in \mathbb{N}, 0 < k \implies \operatorname{finite}\left(\operatorname{O}\left(k\right)\right) \land \operatorname{ncard}\left(\operatorname{O}\left(k\right)\right) = 9+\mathbf{1}_{k=1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CounterSequences/LeadingCounter.leading_counter_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David James Sycamore (2025). *A384309 — the leading decimal digit counter sequence*. URL: <https://oeis.org/A384309>.

*Commentary.*

O(k) denotes the set of natural positions n for which a(n)=k; ncard is its cardinality, and the indicator is one exactly when k=1. Finiteness is part of the conclusion.

Some digit class occurs infinitely often by the infinite pigeonhole principle. Its successive visits emit every positive integer. For each digit d, the numbers d times powers of ten are distinct and have leading digit d, so every digit class occurs infinitely often.

Fix a positive k. Send each successor occurrence of k to the digit class of its predecessor. This is injective because a counter never repeats a value when incremented, and surjective because every counter has a k-th visit. Thus there are nine successor occurrences. The initial position contributes one more exactly for k=1.

## References

- Truth anchor: `D5/S3/Arith/CounterSequences/LeadingCounter.a_one`
- Truth anchor: `D5/S3/Arith/CounterSequences/LeadingCounter.a_recurrence`
- Truth anchor: `D5/S3/Arith/CounterSequences/LeadingCounter.leading_counter_multiplicity`
