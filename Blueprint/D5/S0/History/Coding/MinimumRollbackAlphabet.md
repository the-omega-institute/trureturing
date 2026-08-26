# Minimum Rollback Alphabet

## Abstract

Exact finite rollback logs need as many labels as the largest process fiber.

**Theorem 1.1 (The largest process fiber is the minimum rollback alphabet).**

$$\forall X, Y: \operatorname{Type},\ [\operatorname{Finite} X] [\operatorname{Fintype} Y],\ U: X \to Y,\\m_{U} = \max_{y\in Y} \Vert \{x: X \mid U(x) = y\} \Vert,\\(\forall M: \operatorname{Type}, [\operatorname{Finite} M], L: X \to M,\\\operatorname{Injective}(x \mapsto (U(x), L(x))) \Rightarrow m_{U} \leq \Vert M \Vert) \land\\\exists L: X \to \operatorname{Fin}(m_{U}), \operatorname{Injective}(x \mapsto (U(x), L(x))).$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Coding/MinimumRollbackAlphabet.minimum_rollback_alphabet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite state types X and Y and a process U from X to Y, the number mU is computed as the maximum cardinality of an actual fiber of U. Every log whose paired process-log record is injective has an alphabet of cardinality at least mU.

Conversely, each fiber is enumerated independently and embedded into the common type Fin mU. Equal process outputs then place two states in the same fiber, while equal labels force equality inside that enumeration, so the paired record is injective.

Pinned Mathlib supplies Nat.card_le_card_of_injective, Finite.equivFin, Fin.castLEEmb, Finset.le_sup, and Finset.sup_le. Repository and pinned-Mathlib searches found no declaration packaging the complete lower bound and attaining construction.

## References

- Truth anchor: `D5/S0/History/Coding/MinimumRollbackAlphabet.minimum_rollback_alphabet`
