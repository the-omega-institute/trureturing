# Prime Digit Bases

## Abstract

Two certificates cover every argument above nine, leaving five exceptions below it.

Digit lists are little-endian, so the pair written two-two appears as the list with two twice and the pair written two-three appears with three first. The empty list of the zero argument is why that argument is excluded explicitly: a condition quantified over an empty list holds vacuously, which would otherwise admit it.

**Definition 1.1 (The condition).**

$$\forall n \in \mathbb{N}, \operatorname{HasPrimeDigitBase}\left(n\right) \iff n \neq 0 \land \exists b, 1 < b \land \forall d \in \operatorname{digits}\left(b, n\right), \operatorname{Prime}\left(d\right)$$

*Formalization.* `D5/S1/Digit/PrimeDigitBaseClassification.HasPrimeDigitBase` (`✓ std3`).

*Citation.* OEIS Foundation Inc. (2025). *OEIS A390088*. URL: <https://oeis.org/A390088>.

*Commentary.*

Some base above one writes the argument with every digit prime. The argument being nonzero is part of the condition, not an afterthought.

**Theorem 1.2 (Two certificates above nine).**

$$\forall n \in \mathbb{N}, 10 \leq n \Rightarrow (\operatorname{digits}\left(\frac{n - 2}{2}, n\right) = \{2, 2\}) \lor (\operatorname{digits}\left(\frac{n - 3}{2}, n\right) = \{3, 2\})$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeDigitBaseClassification.prime_digit_base_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An even argument is two more than twice half of two less than it, and an odd argument is three more than twice half of three less than it. Each gives a two-digit representation whose digits are prime and below the base. The statement is an equality of digit lists, not merely existence.

**Theorem 1.3 (The exception set).**

$$\forall n \in \mathbb{N}, \operatorname{HasPrimeDigitBase}\left(n\right) \iff \neg {n \in \{0, 1, 4, 6, 9\}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeDigitBaseClassification.a390088` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a390088-prime-digit-base-existence` (proved) by `D5/S1/Digit/PrimeDigitBaseClassification.a390088`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a390088-prime-digit-base-existence","declaration_gid":"D5/S1/Digit/PrimeDigitBaseClassification.a390088","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc. (2025). *OEIS A390088*. URL: <https://oeis.org/A390088>.

*Commentary.*

Above nine the certificates apply. Below it the question is finite: four arguments admit no base, the zero argument is excluded by the condition itself, and the rest admit one, of which a single argument admits only one base. For nonexistence, split on whether the argument is below the base; if it is, the digit list is a singleton and primality is direct, and if it is not, the base is small too and a bounded enumeration ends it.

The least such base, which is what the source's sequence records, is not formalized here; only the existence question the conjecture asks.

## References

- Truth anchor: `D5/S1/Digit/PrimeDigitBaseClassification.HasPrimeDigitBase`
- Truth anchor: `D5/S1/Digit/PrimeDigitBaseClassification.a390088`
- Truth anchor: `D5/S1/Digit/PrimeDigitBaseClassification.prime_digit_base_certificate`
