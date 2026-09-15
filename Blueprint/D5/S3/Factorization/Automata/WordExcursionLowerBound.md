# An Excursion Lower Bound on Word Length

## Abstract

A word is at least as long as twice its excursion width minus the absolute value of its net displacement.

A word is a finite list of booleans, each letter moving an integer coordinate up by one or down by one. The three functions below read that walk: its net displacement, the least coordinate it reaches, and the greatest. Both extrema include the empty prefix, so they bracket zero. All values are integers and the length of the word is cast to an integer.

**Definition 1.1 (Net displacement of a word).**

$$displacement\left([]\right) = 0 \land \forall b \in Bool, \forall w \in List\left(Bool\right), displacement\left(b :: w\right) = (if b then 1 else -1) + displacement\left(w\right)$$

*Formalization.* `D5/S3/Factorization/Automata/WordExcursionLowerBound.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word displaces nothing. A letter contributes plus one when it is true and minus one when it is false, and the rest of the word contributes its own displacement.

**Definition 1.2 (Least coordinate reached).**

$$low\left([]\right) = 0 \land \forall b \in Bool, \forall w \in List\left(Bool\right), low\left(b :: w\right) = min\left(0, (if b then 1 else -1) + low\left(w\right)\right)$$

*Formalization.* `D5/S3/Factorization/Automata/WordExcursionLowerBound.low` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word reaches only zero. For a nonempty word the least coordinate is the smaller of zero and the first letter's step added to the least coordinate of the rest, so the empty prefix is included and the value is never positive.

**Definition 1.3 (Greatest coordinate reached).**

$$high\left([]\right) = 0 \land \forall b \in Bool, \forall w \in List\left(Bool\right), high\left(b :: w\right) = max\left(0, (if b then 1 else -1) + high\left(w\right)\right)$$

*Formalization.* `D5/S3/Factorization/Automata/WordExcursionLowerBound.high` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dually, the greatest coordinate is the larger of zero and the first letter's step added to the greatest coordinate of the rest; it is never negative.

**Theorem 1.4 (Length bounds the excursion).**

$$\forall w \in List\left(Bool\right), 2 \times \left(high\left(w\right) - low\left(w\right)\right) - max\left(displacement\left(w\right), -displacement\left(w\right)\right) \leq length\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/WordExcursionLowerBound.word_length_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every word is at least as long as twice the width it explores, minus the absolute value of what it finally achieves. The bound is stated for every word, not for a chosen representative. A word that returns to its start has zero displacement, so the bound charges it twice its full width: reaching an extreme coordinate and coming back are both paid for. The proof inducts on the word, and the inductive hypothesis supplies exactly the bracketing of the displacement between the two extrema that the step needs.

## References

- Truth anchor: `D5/S3/Factorization/Automata/WordExcursionLowerBound.displacement`
- Truth anchor: `D5/S3/Factorization/Automata/WordExcursionLowerBound.high`
- Truth anchor: `D5/S3/Factorization/Automata/WordExcursionLowerBound.low`
- Truth anchor: `D5/S3/Factorization/Automata/WordExcursionLowerBound.word_length_lower_bound`
