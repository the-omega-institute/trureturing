# Infinite Greedy Stream for Beta13

## Abstract

An exact quadratic-state recurrence defines the infinite greedy beta13 stream, its all-length suffix criterion, and an independent level-six gap count.

Integer pairs encode every remainder exactly because beta13 squared is beta13 plus three. An executable integer comparison selects each floor digit without floating-point approximation.

**Theorem 1.1 (Exact remainder recurrence).**

$$\forall n \in N,\; \operatorname{beta13RemainderValue}\left(n + 1\right) = \mathit{beta13} \cdot \operatorname{beta13RemainderValue}\left(n\right) - \operatorname{beta13GreedyDigit}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_value_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real interpretation of the next exact pair is beta13 times the current remainder minus the selected integer digit.

**Theorem 1.2 (Remainders stay in the unit interval).**

$$\forall n \in N,\; 0 \le \operatorname{beta13RemainderValue}\left(n\right) \land \operatorname{beta13RemainderValue}\left(n\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_value_in_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction identifies every successor with a fractional part, so all remainders lie between zero and one.

**Theorem 1.3 (Every digit is the greedy floor digit).**

$$\forall n \in N,\; \operatorname{beta13GreedyDigit}\left(n\right) = \left\lfloor\mathit{beta13} \cdot \operatorname{beta13RemainderValue}\left(n\right)\right\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_digit_eq_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact sign comparison and the invariant interval identify the chosen digit with the real floor at every index.

**Theorem 1.4 (The stream obeys the greedy floor recurrence).**

$$\forall n \in N,\; \operatorname{beta13RemainderValue}\left(n + 1\right) = \mathit{beta13} \cdot \operatorname{beta13RemainderValue}\left(n\right) - \left\lfloor\mathit{beta13} \cdot \operatorname{beta13RemainderValue}\left(n\right)\right\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_floor_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the floor identity gives the standard greedy beta transformation recurrence for every natural index.

**Theorem 1.5 (Threaded prefixes come from the infinite stream).**

$$\forall Q \in N,\; \operatorname{beta13GreedyPrefix}\left(Q\right) = \operatorname{ofFn}\left(Q, \mathit{beta13GreedyDigit}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_prefix_eq_ofFn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The efficient state-threading implementation agrees pointwise with the unbounded digit function at every finite length.

**Theorem 1.6 (The prefix test is valid at every length).**

$$\forall w \in \operatorname{List}\left(Z\right),\; \operatorname{beta13BelowGreedyPrefix}\left(w\right) = \mathit{true} \Leftrightarrow \operatorname{compare}\left(w, \operatorname{ofFn}\left(\operatorname{length}\left(w\right), \mathit{beta13GreedyDigit}\right)\right) \ne \mathit{greater}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_below_greedy_prefix_iff_infinite_stream` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unlike the frozen ten-digit list, the Boolean test compares each word with the equally long prefix of the infinite digit function.

**Theorem 1.7 (The generator matches the all-suffix criterion).**

$$\forall Q \in N,\; \forall w \in \operatorname{List}\left(Z\right),\; w \in \operatorname{beta13Names}\left(Q\right) \Leftrightarrow \left(\operatorname{length}\left(w\right) = Q \land \operatorname{Beta13Admissible}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.mem_beta13_names_iff_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every level, recursive generator membership is equivalent to the declared length, alphabet membership, and the infinite-prefix test for every suffix.

**Theorem 1.8 (The infinite-prefix model has six level-six gap types).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(6\right)\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_infinite_gap_type_count_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A default-depth, chunked exact certificate recomputes the level-six spectrum without using any frozen gap-count theorem.

## References

- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_below_greedy_prefix_iff_infinite_stream`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_digit_eq_floor`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_prefix_eq_ofFn`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_infinite_gap_type_count_six`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_floor_recurrence`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_value_in_unit_interval`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_value_succ`
- Truth anchor: `D5/S0/Tower/NonPisot/Beta13Infinite.mem_beta13_names_iff_admissible`
- Dependency: [D5/S0/Tower/NonPisot/Beta13](Beta13.md)
