# Bounded State Sample Compactness

## Abstract

Finite samples characterize bounded-state output automata.

**Theorem 1.1 (Finite obstructions for a fixed state budget).**

$$\operatorname{Realizable}(s, D, f) \iff \forall E \subseteq D, \operatorname{Finite}(E) \Rightarrow \operatorname{Realizable}(s, E, f).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/BoundedStateSampleCompactness.bounded_state_sample_compactness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and Y be finite alphabets, D any set of words over A, f a function from D to Y, and s a natural number. Realizable(s,E,f) means that some finite state type Q with cardinality at most s supports a total deterministic output automaton whose output on every word in E equals f at that word. State types and alphabets may lie in arbitrary universes. No labels are imposed outside D.

Global correctness restricts to every finite sample. Conversely, embed each state type of size at most s into Fin s, extend the transitions through a retraction, and read the original outputs through that retraction. Induction on words shows that all reached states and outputs are preserved.

A candidate on Fin s is determined by its initial state, transition table, and output table; the acceptance set is irrelevant to output evaluation. These tables form a finite product. If every candidate fails on D, choose one failing word for each table. Their finite image excludes every candidate, contradicting realizability of every finite sample.

$\operatorname{card}(Tables) = s s^{s \operatorname{card}(A)} \operatorname{card}(Y)^{s}.$

Consequently, global nonexistence has a finite sample obstruction. A sound unsatisfiability certificate for exact sample labels therefore excludes a global machine with the same state budget. Satisfiability of one sample gives no such global conclusion. The argument supplies no effective bound on the lengths of the failing words.

The equivalence includes empty domains, empty output alphabets, and zero state budgets. In particular it applies when Y is nonempty and s is positive. Every sample family includes the empty sample; an automaton must still have an initial state and an output map.

## References

- Truth anchor: `D5/S0/Automata/BoundedStateSampleCompactness.bounded_state_sample_compactness`
- Dependency: [D5/S0/Automata/FiniteSampleRestriction](FiniteSampleRestriction.md)
