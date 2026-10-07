# Palindrome reflection forces the paired endpoint language

## Abstract

Palindrome reflection forces the paired endpoint language

**Theorem 1.1 (palindrome_endpoint).**

$$\forall u \in List\left(Fin\left(2\right)\right),\; \forall v \in List\left(Fin\left(2\right)\right),\; \left(NoAdjacentOnes\left(u\right) \land \left(NoAdjacentOnes\left(v\right) \land \left(length\left(u\right) = length\left(v\right) \land \left(fst\left(fibPair\left(u\right)\right) < fst\left(fibPair\left(v\right)\right) \land Palindrome\left(goldenFactor\left(fst\left(fibPair\left(v\right)\right) - fst\left(fibPair\left(u\right)\right), fst\left(fibPair\left(u\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow mem\left(zip\left(u, v\right), accepts\left(endpoint\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The words are equal-width canonical Zeckendorf encodings, allowing leading zeros. Their values are the half-open interval endpoints. Canonical last digits determine goldenWord letters through wdigits. A mismatch path would give two reflected positions with different letters, contradicting palindrome reflection. The finite complement monitor therefore forces an accepting endpoint path. This assertion proves the required recognizer necessity directly; it does not assert the arithmetic CanonicalEdge equivalence.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton](EndpointAutomaton.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/MismatchWitness](MismatchWitness.md)
