# Bounded complete residual representatives

## Abstract

Bounded complete residual representatives.

**Definition 1.1 (Iterated source tile).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualCover.tile`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualCover.tile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a : Bool × Bool, tile 0 a = [a] and tile (H + 1) a = (mu a).flatMap (tile H). These are iterates of the same decorated source substitution.

**Definition 1.2 (Numerical source prefix).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualCover.sourcePrefix`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualCover.sourcePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n : ℕ, sourcePrefix n = (List.range n).map q, the first n letters of the actual decorated numerical source.

**Theorem 1.3 (Bounded complete residual representatives).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualCover.all_state_cover`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidualCover.all_state_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem all_state_cover (H c : ℕ) (hH : 14 ≤ H) (hc : c ≤ Nat.fib H) (w : List (Fin 2)) (hw : NoAdjacentOnes w) : ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧ residual c w = residual c v`.

Every legal padded prefix has the same complete Option residual as a legal word of length H+7 whenever c≤F_H and H≥14. Iterated numerical substitution tiles realize every adjacent source pair in a finite prefix.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfResidualCover.all_state_cover`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualCover.sourcePrefix`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualCover.tile`
- Dependency: [D5/S1/Digit/GoldenBase4DenseInput](GoldenBase4DenseInput.md)
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](GoldenZeckendorfLanguage.md)
- Dependency: [D5/S1/Digit/ZeckendorfRawWindow](ZeckendorfRawWindow.md)
