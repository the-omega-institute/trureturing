# Decorated Fibonacci Windows

## Abstract

Actual canonical Fibonacci parity windows carry complete partial continuation behavior.

**Definition 1.1 (Occupied Fibonacci indices).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.support`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a padded MSD word w over Fin 2, support [] = [] and support (a :: w) = support w if a = 0, otherwise (w.length + 2) :: support w. Indices descend in MSD order; legal words have no adjacent occupied indices.

**Definition 1.2 (Padded MSD value).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.value`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every w : List (Fin 2), value w = (fibPair w).1. Thus the rightmost position has weight F_2 = 1; prepended zeros preserve the value.

**Definition 1.3 (Canonical Fibonacci parity).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.parity`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n : ℕ, parity n = decide ((wdigits n).length % 2 = 1), the parity of the occupied indices of the canonical Zeckendorf representation.

**Definition 1.4 (Decorated numerical source).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.q`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n : ℕ, q n = (parity n, decide (2 ∈ wdigits n)). The two coordinates record canonical parity and occupation of the least Fibonacci position.

**Definition 1.5 (Decorated substitution).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.mu`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.mu` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a : Bool × Bool, mu a is [(a.1, false)] when a.2 is true, and [(a.1, false), (!a.1, true)] otherwise. Both decorations are retained in the substituted source.

**Definition 1.6 (Complete decorated window).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.window`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c n : ℕ, window c n = (List.range (c + 1)).map (fun i => q (n + i)). It includes both numerical endpoints n and n + c.

**Definition 1.7 (Complete partial continuation).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.residual`

*Formalization.* `D5/S1/Digit/ZeckendorfRawWindow.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c : ℕ and w z : List (Fin 2), residual c w z is some (parity (value (w ++ z) + c)) when NoAdjacentOnes (w ++ z), and none otherwise. The domain includes every padded legal word and the empty suffix; malformed continuations remain undefined.

**Theorem 1.8 (Padded source coordinates).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem source_word_coordinates (w : List (Fin 2)) (hw : NoAdjacentOnes w) : (support w).IsZeckendorfRep ∧ (∀ k ∈ support w, k < w.length + 2) ∧ ((support w).map Nat.fib).sum = (fibPair w).1 ∧ ((support w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2`.

Every legal padded MSD word has canonical occupied indices. The same indices decode the value and its one-position Fibonacci shift.

**Theorem 1.9 (Numerical substitution intervals).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.source_expansion`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfRawWindow.source_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem source_expansion (n t : ℕ) : ((List.range t).map (fun i => q (n + i))).flatMap mu = (List.range (goldenSubstStart (n + t) - goldenSubstStart n)).map (fun i => q (goldenSubstStart n + i))`.

Substituting the decorated letters of a numerical interval yields exactly the interval between the corresponding append-zero boundaries. The four images retain parity and the least occupied digit.

**Theorem 1.10 (Complete partial residual congruence).**

Lean statement: `D5/S1/Digit/ZeckendorfRawWindow.window_residual_congruence`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfRawWindow.window_residual_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem window_residual_congruence (c : ℕ) (w v : List (Fin 2)) (hw : NoAdjacentOnes w) (hv : NoAdjacentOnes v) (he : window c (value w) = window c (value v)) : residual c w = residual c v`.

Equality of actual windows implies equality on every suffix, including the empty suffix. The least-digit occupation at the first window position controls extension legality; the parity at the final window position supplies the terminal output. Invalid continuations give none on both sides.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.mu`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.parity`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.q`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.residual`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.source_expansion`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.support`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.value`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.window`
- Truth anchor: `D5/S1/Digit/ZeckendorfRawWindow.window_residual_congruence`
- Dependency: [D5/S0/Automata/BinaryZeckendorfLanguage](../../S0/Automata/BinaryZeckendorfLanguage.md)
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](GoldenBase4IntervalMachine.md)
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf](../Words/Powers/GoldenDesubstitutionZeckendorf.md)
