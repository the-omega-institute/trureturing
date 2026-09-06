# Arithmetic Inputs in the Base Language

## Abstract

Canonical dense Zeckendorf words execute in the binary base for every natural number.

**Theorem 1.1 (All canonical MSD inputs execute successfully).**

$$\forall n : Nat, \exists q : BinaryZeckendorfState, \operatorname{evalBinaryZeckendorfBase}\left(\operatorname{zeckendorfMSDWord}\left(n\right)\right) = \operatorname{some}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenZeckendorfLanguage.zeckendorfMSDWord_base_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, including zero, the existing zeckendorfMSDWord generator is accepted from previousZero. The proof uses Mathlib's gap-separated occupied-index predicate and its list chain API to transfer nonadjacency through the reversed-range dense rendering.

The theorem has no finite sample bound. It uses the current GoldenBase4AutomataOracle generator and does not assume the separate IsZeckendorfBitWord predicate described in the paper's alternate source.

**Theorem 1.2 (Every sparse radix-four input executes in its base).**

$$\forall i : Nat, \exists q : BinaryZeckendorfState, \operatorname{evalBase4ProblemBase}\left(\operatorname{base4ProblemInput}\left(i\right)\right) = \operatorname{some}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenZeckendorfLanguage.base4PowerWord_base_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Instantiate the natural-number theorem at 4 raised to i. The input and base are precisely the fields of the existing base4Problem; no correct candidate machine or solver certificate is assumed.

## References

- Truth anchor: `D5/S1/Digit/GoldenZeckendorfLanguage.base4PowerWord_base_success`
- Truth anchor: `D5/S1/Digit/GoldenZeckendorfLanguage.zeckendorfMSDWord_base_success`
- Dependency: [D5/S0/Automata/BinaryZeckendorfLanguage](../../S0/Automata/BinaryZeckendorfLanguage.md)
- Dependency: [D5/S1/Digit/GoldenDFAOMinimalityTargets](GoldenDFAOMinimalityTargets.md)
