# Canonical digit order and Fibonacci value

## Abstract

Canonical digit order and Fibonacci value

**Theorem 1.1 (canonical_lex_value).**

$$\forall u \in List\left(Fin\left(2\right)\right),\; \forall v \in List\left(Fin\left(2\right)\right),\; \left(NoAdjacentOnes\left(u\right) \land \left(NoAdjacentOnes\left(v\right) \land length\left(u\right) = length\left(v\right)\right)\right) \Rightarrow \left(fst\left(fibPair\left(u\right)\right) < fst\left(fibPair\left(v\right)\right) \Leftrightarrow Lex\left(\lambda (a:Fin\left(2\right)) \mapsto \lambda (b:Fin\left(2\right)) \mapsto a < b, u, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics.canonical_lex_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Leading zero digits are permitted. NoAdjacentOnes forbids consecutive one digits. Equal-width canonical words are ordered numerically exactly as they are lexicographically; the strict tail bound follows from the Fibonacci recurrence.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics.canonical_lex_value`
- Dependency: [D5/S1/Digit/ZeckendorfRawWindow](../../../Digit/ZeckendorfRawWindow.md)
