# Archive Clock Recovery

## Abstract

Finite synchronized executions characterize archive-clock recovery and bound its first ambiguity.

**Definition 1.1 (Finite partial-action systems).**

$$\begin{aligned}\forall X, A, Y: Type,\\\operatorname{System}\left(X, A, Y\right) = \{D: A \to X \to Prop, F: A \to X \to X,\\{}ell: \forall a: A, \forall x: X, \operatorname{D}\left(a, x\right) \to Y, c: A \to X \to \mathbb{Z},\\{}\forall a, x, \operatorname{Decidable}\left(\operatorname{D}\left(a, x\right)\right)\}.\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.System` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A system assigns to each action a decidable domain, a total successor and integer cost, and a reading defined only on that action's domain. Values outside the domain never enter a legal execution, so this preserves the source partial-map model, including empty reading types and empty domains.

**Definition 1.2 (State after an action word).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x: X,\\\operatorname{stateAfter}\left(S, x, []\right) = x,\\\forall a: A, \forall w: \operatorname{List}\left(A\right), \operatorname{stateAfter}\left(S, x, \operatorname{cons}\left(a, w\right)\right) = \operatorname{stateAfter}\left(S, \operatorname{successor}\left(S, a, x\right), w\right).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.stateAfter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state after the empty word is the initial state. For a nonempty word, the first action changes the state and the remaining actions are then evaluated.

**Definition 1.3 (Legal executions).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x: X,\\\operatorname{Legal}\left(S, x, []\right),\\\forall a: A, \forall w: \operatorname{List}\left(A\right), (\operatorname{Legal}\left(S, x, \operatorname{cons}\left(a, w\right)\right)) \iff ((\operatorname{domain}\left(S, a, x\right)) \land (\operatorname{Legal}\left(S, \operatorname{successor}\left(S, a, x\right), w\right))).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty execution is legal. A nonempty execution is legal exactly when its first action is defined at the current state and its tail is legal from the successor.

**Definition 1.4 (Visible archives).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x: X,\\\operatorname{visibleArchive}\left(S, x, []\right) = [],\\\forall a: A, \forall w: \operatorname{List}\left(A\right), \operatorname{visibleArchive}\left(S, x, \operatorname{cons}\left(a, w\right)\right) = \operatorname{dite}\left(\operatorname{domain}\left(S, a, x\right), \lambda h \mapsto \operatorname{cons}\left(\operatorname{pair}\left(a, \operatorname{reading}\left(S, a, x, h\right)\right), \operatorname{visibleArchive}\left(S, \operatorname{successor}\left(S, a, x\right), w\right)\right), \lambda h \mapsto []\right).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.visibleArchive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each execution step records the chosen action together with the reading produced at the state where that action is taken.

**Definition 1.5 (Accumulated clock).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x: X,\\\operatorname{clock}\left(S, x, []\right) = 0,\\\forall a: A, \forall w: \operatorname{List}\left(A\right), \operatorname{clock}\left(S, x, \operatorname{cons}\left(a, w\right)\right) = \operatorname{cost}\left(S, a, x\right) + \operatorname{clock}\left(S, \operatorname{successor}\left(S, a, x\right), w\right).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.clock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The clock of an execution is the sum of the integer costs of its actions at their successive source states.

**Definition 1.6 (Synchronized edges).**

$$\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall p: \operatorname{Prod}\left(X, X\right), \forall a: A, (\operatorname{SynchronizedEdge}\left(S, p, a\right)) \iff (\exists h: \operatorname{domain}\left(S, a, \operatorname{fst}\left(p\right)\right), \exists h': \operatorname{domain}\left(S, a, \operatorname{snd}\left(p\right)\right), \operatorname{reading}\left(S, a, \operatorname{fst}\left(p\right), h\right) = \operatorname{reading}\left(S, a, \operatorname{snd}\left(p\right), h'\right)).$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronizedEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A synchronized edge applies one action legally to two states and requires the two visible readings for that action to agree.

**Definition 1.7 (Synchronized paths).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x, x': X,\\\operatorname{SynchronizedPath}\left(S, x, x', []\right),\\\forall a: A, \forall w: \operatorname{List}\left(A\right), (\operatorname{SynchronizedPath}\left(S, x, x', \operatorname{cons}\left(a, w\right)\right)) \iff ((\operatorname{SynchronizedEdge}\left(S, \operatorname{pair}\left(x, x'\right), a\right)) \land (\operatorname{SynchronizedPath}\left(S, \operatorname{successor}\left(S, a, x\right), \operatorname{successor}\left(S, a, x'\right), w\right))).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronizedPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A synchronized path follows the same action word from two states, with a synchronized edge at every step.

**Definition 1.8 (Synchronized pair traces).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x, x': X,\\\operatorname{pairTrace}\left(S, x, x', []\right) = \operatorname{singleton}\left(\operatorname{pair}\left(x, x'\right)\right),\\\forall a: A, \forall w: \operatorname{List}\left(A\right), \operatorname{pairTrace}\left(S, x, x', \operatorname{cons}\left(a, w\right)\right) = \operatorname{cons}\left(\operatorname{pair}\left(x, x'\right), \operatorname{pairTrace}\left(S, \operatorname{successor}\left(S, a, x\right), \operatorname{successor}\left(S, a, x'\right), w\right)\right).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.pairTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair trace contains the initial state pair and every successive pair reached by the common action word.

**Definition 1.9 (Clock-difference sums).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall x, x': X,\\\operatorname{deltaSum}\left(S, x, x', []\right) = 0,\\\forall a: A, \forall w: \operatorname{List}\left(A\right), \operatorname{deltaSum}\left(S, x, x', \operatorname{cons}\left(a, w\right)\right) = (\operatorname{cost}\left(S, a, x\right) - \operatorname{cost}\left(S, a, x'\right)) + \operatorname{deltaSum}\left(S, \operatorname{successor}\left(S, a, x\right), \operatorname{successor}\left(S, a, x'\right), w\right).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.deltaSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The delta sum accumulates, edge by edge, the first execution's cost minus the second execution's cost.

**Definition 1.10 (Synchronous reachability).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall X0: \operatorname{Set}\left(X\right), \forall p: \operatorname{Prod}\left(X, X\right),\\(\operatorname{SynchronouslyReachable}\left(S, X0, p\right)) \iff (\exists x, x': X, \exists w: \operatorname{List}\left(A\right), (((x \in X0) \land (x' \in X0)) \land (\operatorname{SynchronizedPath}\left(S, x, x', w\right))) \land (\operatorname{pair}\left(\operatorname{stateAfter}\left(S, x, w\right), \operatorname{stateAfter}\left(S, x', w\right)\right) = p)).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronouslyReachable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pair is synchronously reachable when a common synchronized word carries two allowed initial states to that pair.

**Definition 1.11 (Recovery from visible archives).**

$$\begin{aligned}\forall X, A, Y: Type, \forall S: \operatorname{System}\left(X, A, Y\right), \forall X0: \operatorname{Set}\left(X\right),\\(\operatorname{ArchiveRecoverable}\left(S, X0\right)) \iff (\exists Gamma: \operatorname{List}\left(\operatorname{Prod}\left(A, Y\right)\right) \to \mathbb{Z}, \forall x: X, \forall w: \operatorname{List}\left(A\right), ((x \in X0) \land (\operatorname{Legal}\left(S, x, w\right))) \Rightarrow (\operatorname{Gamma}\left(\operatorname{visibleArchive}\left(S, x, w\right)\right) = \operatorname{clock}\left(S, x, w\right))).\end{aligned}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.ArchiveRecoverable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Archive recoverability means that one integer-valued function of the visible archive equals the clock on every legal execution from every allowed initial state.

**Theorem 1.12 (Archive recovery is equivalent to synchronized cost consistency).**

$$\begin{aligned}\forall X, A, Y: Type, \forall n: \mathbb{N},\\\forall X0: \operatorname{Set}\left(X\right), \forall S: \operatorname{System}\left(X, A, Y\right),\\(((\operatorname{Fintype}\left(X\right)) \land ((\operatorname{Fintype}\left(A\right)) \land (\operatorname{Fintype}\left(Y\right)))) \land ((\operatorname{card}\left(X\right) = n) \land (\operatorname{Nonempty}\left(X0\right)))) \Rightarrow ((((\operatorname{ArchiveRecoverable}\left(S, X0\right)) \iff (\forall x, x': X, \forall w: \operatorname{List}\left(A\right), (((x \in X0) \land (x' \in X0)) \land (\operatorname{SynchronizedPath}\left(S, x, x', w\right))) \Rightarrow (\operatorname{deltaSum}\left(S, x, x', w\right) = 0))) \land ((\forall x, x': X, \forall w: \operatorname{List}\left(A\right), (((x \in X0) \land (x' \in X0)) \land (\operatorname{SynchronizedPath}\left(S, x, x', w\right))) \Rightarrow (\operatorname{deltaSum}\left(S, x, x', w\right) = 0)) \iff (\forall p: \operatorname{Prod}\left(X, X\right), \forall a: A, ((\operatorname{SynchronouslyReachable}\left(S, X0, p\right)) \land (\operatorname{SynchronizedEdge}\left(S, p, a\right))) \Rightarrow (\operatorname{cost}\left(S, a, \operatorname{fst}\left(p\right)\right) - \operatorname{cost}\left(S, a, \operatorname{snd}\left(p\right)\right) = 0)))) \land ((\neg \operatorname{ArchiveRecoverable}\left(S, X0\right)) \Rightarrow (\exists x, x': X, \exists w: \operatorname{List}\left(A\right), (((x \in X0) \land (x' \in X0)) \land ((\operatorname{Legal}\left(S, x, w\right)) \land (\operatorname{Legal}\left(S, x', w\right)))) \land ((\operatorname{visibleArchive}\left(S, x, w\right) = \operatorname{visibleArchive}\left(S, x', w\right)) \land ((\operatorname{clock}\left(S, x, w\right) \neq \operatorname{clock}\left(S, x', w\right)) \land (\operatorname{length}\left(w\right) \leq n^{2})))))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite configuration, action, and reading types, with n configurations and a nonempty allowed initial set, three conditions are equivalent: a single archive decoder recovers every legal clock, every synchronized path from allowed initial states has zero delta sum, and every synchronized edge whose source pair is synchronously reachable has zero cost difference.

Two synchronized executions have the same visible archive, and their delta sum is exactly the difference of their clocks. Conversely, equality of visible archives synchronizes the two executions. Prefix subtraction turns zero path sums into zero reachable-edge differences.

If recovery fails, choose a shortest synchronized word reaching the source of a nonzero edge. A repeated state pair would allow the intervening loop to be removed while preserving legality, readings, and the endpoint, contradicting minimality. Thus its pair trace has at most n squared vertices. According to whether the prefix delta is already nonzero, the prefix or the prefix followed by the bad edge gives equal archives, unequal clocks, and common length at most n squared.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.ArchiveRecoverable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.Legal`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronizedEdge`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronizedPath`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.SynchronouslyReachable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.System`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.clock`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.deltaSum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.pairTrace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.stateAfter`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.visibleArchive`
