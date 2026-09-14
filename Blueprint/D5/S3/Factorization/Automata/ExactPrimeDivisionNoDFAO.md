# Exact Prime Division Defeats Every Finite Automaton

## Abstract

A prime multiply-divide register defeats every finite-state automaton at each positive power.

Fix a prime p and an exponent a with a at least one. A register holds a natural number, starts at one, and reads a word over two letters: true multiplies by p, and false divides by p and is undefined unless p divides the current value. A word is legal when every step is defined, and the reached values along legal words are exactly the powers of p. The question asked of a machine is a single bit: does the integer reached carry p to the power a as a divisor. The theorem says no machine with finitely many states answers that question correctly on every legal word. Both restrictions are used. At a equal to zero the bit is constantly true and one state suffices, and on positional numerals rather than multiply and divide histories a remainder automaton modulo p to the power a decides the same divisibility.

**Theorem 1.1 (No finite automaton decides the threshold).**

$$\forall p \in Nat, \forall a \in Nat, Prime\left(p\right) \land 0 < a \implies \forall register : PartialDFA\left(Bool, Nat\right), \left(start\left(register\right) = 1 \land \forall n \in Nat, \forall u \in Bool, step\left(register, n, u\right) = if u then some\left(n \times p\right) else if p \mid n then some\left(n / p\right) else none\right) \implies \forall S \in Type, \left(Finite\left(S\right) \implies \forall M : DFAO\left(Bool, Bool, S\right), \neg \left(\forall w \in List\left(Bool\right), \forall n \in Nat, eval\left(register, w\right) = some\left(n\right) \implies \left(evalOutput\left(M, w\right) = true \iff p^{a} \mid n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/ExactPrimeDivisionNoDFAO.no_finite_dfao_for_exact_prime_division` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The register is presented by its two defining equations rather than by a name, so the statement quantifies over every partial automaton on the natural numbers that starts at one and steps by that guarded arithmetic. Correctness is written out: on every word whose run is defined and reaches n, the machine's output bit agrees with whether p to the power a divides n. Nothing is demanded on words the register cannot run. The content is the construction. For a machine with n states the proof exhibits n + 1 legal prefixes, the prefix of index i being a + i multiplications, together with, for each pair of distinct indices, a continuation of exactly the smaller index plus one divisions on which the demanded bit differs. That these prefixes are legal and separated rests on an image lemma: the register run started at p to the e is the image under k maps to p to the k of a counter run on the exponent, which is where primality enters through the exact-division guard. The frozen state lower bound takes such a family as a hypothesis and returns n + 1 at most the number of states, contradicting n.

## References

- Truth anchor: `D5/S3/Factorization/Automata/ExactPrimeDivisionNoDFAO.no_finite_dfao_for_exact_prime_division`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](../../../S0/Automata/TypedPartialDFAOOverBase.md)
