# Guarded Walk Factorization

## Abstract

A one-sided strand trace forces a complete descending run.

A strand at one-based position t can move left across generator k when k+1=t. The guard rules out a rightward move across k=t.

**Definition 1.1 (Left step).**

$$\operatorname {leftStep}\left(t, k\right) = \operatorname {ifEq}\left(k + 1, t, k, t\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeGuardedWalk.leftStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position drops to k exactly when k+1=t.

**Definition 1.2 (Trace endpoint).**

$$\operatorname {traceEnd}\left(t, w\right) = \operatorname {foldLeftSteps}\left(t, w\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeGuardedWalk.traceEnd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoint applies leftStep in list order.

**Definition 1.3 (No right step).**

$$\operatorname {leftOnly}\left(t, w\right) \iff \operatorname {everyStepAvoidsCurrentGenerator}\left(t, w\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeGuardedWalk.leftOnly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each next generator differs from the current trace position.

**Theorem 1.4 (Trace monotonicity).**

$$\forall t , \forall w , \operatorname {traceEnd}\left(t, w\right) \le t$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeGuardedWalk.traceEnd_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every trace step stays put or decreases the position.

**Theorem 1.5 (Forced descending run).**

$$i \le j \land \operatorname {Consecutive}\left(w\right) \land \operatorname {leftOnly}\left(j + 1, w\right) \land \operatorname {traceEnd}\left(j + 1, w\right) = i \implies \exists p , \exists q , w = \operatorname {concat}\left(p, \operatorname {desc}\left(j, i\right), q\right) \land \operatorname {PrefixBelow}\left(p, j\right) \land \operatorname {SuffixAbove}\left(q, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeGuardedWalk.forced_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix letter is less than j and every suffix letter is greater than i. The result is for arbitrary finite words and unbounded indices.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeGuardedWalk.forced_descent`
- Truth anchor: `D5/S1/Words/Permutations/MamedeGuardedWalk.leftOnly`
- Truth anchor: `D5/S1/Words/Permutations/MamedeGuardedWalk.leftStep`
- Truth anchor: `D5/S1/Words/Permutations/MamedeGuardedWalk.traceEnd`
- Truth anchor: `D5/S1/Words/Permutations/MamedeGuardedWalk.traceEnd_le`
- Dependency: [D5/S1/Words/Permutations/MamedeAdjacentWords](MamedeAdjacentWords.md)
