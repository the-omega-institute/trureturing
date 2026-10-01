# Actual finite partial machines

## Abstract

Actual finite partial machines.

**Definition 1.1 (Exact padded word domain).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualMachine.sourceBase`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualMachine.sourceBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceBase : BaseAutomaton (Fin 2) Bool starts at false. Reading zero moves to some false; reading one moves to some true from false and to none from true. This records the previous-one flag and leaves every input containing 11 undefined.

**Definition 1.2 (Actual live residual image).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualMachine.ResidualState`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualMachine.ResidualState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c : ℕ, ResidualState c is {r : List (Fin 2) → Option Bool // ∃ w, NoAdjacentOnes w ∧ residual c w = r}. Only complete residuals of legal prefixes occur; every state has an actual prefix and the omitted sink is absent.

**Definition 1.3 (Reachable partial MSD machines).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualMachine.Admissible`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualMachine.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c k : ℕ, Admissible c k means ∃ P : BaseAutomaton (Fin 2) (Fin k), ∃ output : Fin k → Bool, P.step P.start 0 = some P.start ∧ (∀ w, (P.run w).map output = residual c [] w) ∧ (∀ s, ∃ w, P.run w = some s). All k states, including the initial state, are reachable and counted. The all-word Option equation requires correct output on every valid padded word and undefined execution on every invalid word. The empty word and every all-zero word output parity c.

**Definition 1.4 (Minimum live state count).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualMachine.minimumStates`

*Formalization.* `D5/S1/Digit/ZeckendorfResidualMachine.minimumStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c : ℕ, minimumStates c = sInf {k | Admissible c k}. Finite residual realization makes this set nonempty. Since it is a set of natural numbers, its infimum is attained; an admissible machine has a start state, so the minimum is positive.

**Theorem 1.5 (Actual finite partial machines).**

Lean statement: `D5/S1/Digit/ZeckendorfResidualMachine.finite_residual_realization`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidualMachine.finite_residual_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement is `theorem finite_residual_realization (c : ℕ) : Finite (ResidualState c) ∧ Admissible c (Nat.card (ResidualState c))`.

The actual residual image is finite for every shift. Its cardinality is realized by a reachable Boolean partial machine whose counted start loops on zero. Execution is defined exactly on all legal padded no11 words, including the empty word. The minimum ranges over ordinary partial transition systems with these complete source equations.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfResidualMachine.Admissible`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualMachine.ResidualState`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualMachine.finite_residual_realization`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualMachine.minimumStates`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidualMachine.sourceBase`
- Dependency: [D5/S0/Automata/TypedPartialDFAO](../../S0/Automata/TypedPartialDFAO.md)
- Dependency: [D5/S1/Digit/ZeckendorfResidualCover](ZeckendorfResidualCover.md)
