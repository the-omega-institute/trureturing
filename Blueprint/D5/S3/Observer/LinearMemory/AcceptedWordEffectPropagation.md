# Accepted words and legal future effects

## Abstract

Actual accepted partial runs generate effect propagation, a simultaneous finite horizon, and arbitrary initial-state delay.

Let K be a division ring and E a left K-module with an additive commutative group. Let Alphabet and Q be arbitrary types, with decidable equality on Q. A BaseAutomaton M has a distinguished start state and partial transition M.step(q,a). Its existing runFrom operation follows the list from left to right, returning none as soon as a transition is absent. Let F be a finite set of accepting states, A assign a total K-linear endomorphism to each letter, and U be the common terminal submodule. No epsilon transitions or intermediate reads are added. For chronological w = a1...ak the effect is the list product A(a1)...A(ak): the head acts after the tail and the empty word acts as identity. Real finite-dimensional spaces are obtained by K = R.

**Definition 1.1 (Actual terminal acceptance).**

$$\forall Alphabet, Q: Type, \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), \forall F: \operatorname{Finset}(Q), \forall q: Q, \forall w: \operatorname{List}(Alphabet), \operatorname{Accepts}(M, F, q, w) = \exists f \in F, \operatorname{runFrom}(M, q, w) = \operatorname{some}(f)$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.Accepts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance requires a successful whole run ending in F. A missing transition supplies no execution event.

**Definition 1.2 (Bounded accepted effect span).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), F: \operatorname{Finset}(Q), A: Alphabet \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \forall n: N, \forall q: Q, \operatorname{acceptedSpan}(M, F, A, U, n, q) = \operatorname{span}(K, \{x \mid \exists w: \operatorname{List}(Alphabet), \operatorname{length}(w) \leq n \land \operatorname{Accepts}(M, F, q, w) \land \exists t \in U, x = \operatorname{apply}(\operatorname{prod}(\operatorname{map}(A, w)), t)\})$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.acceptedSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The span is defined directly from runFrom acceptance and word length, independently of the recurrence.

**Definition 1.3 (All finite accepted effects).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), F: \operatorname{Finset}(Q), A: Alphabet \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \forall q: Q, \operatorname{fullFuture}(M, F, A, U, q) = \operatorname{span}(K, \{x \mid \exists w: \operatorname{List}(Alphabet), \operatorname{Accepts}(M, F, q, w) \land \exists t \in U, x = \operatorname{apply}(\operatorname{prod}(\operatorname{map}(A, w)), t)\})$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.fullFuture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is no length bound. Only accepted terminal reads contribute.

**Definition 1.4 (One propagation step).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), A: Alphabet \to \operatorname{End}(K, E), \forall S: Q \to \operatorname{Submodule}(K, E), \forall q: Q, \operatorname{effectStep}(M, A, S, q) = \operatorname{apply}(S, q) + \operatorname{sup}(a, qprime, \operatorname{step}(M, q, a) = \operatorname{some}(qprime), \operatorname{map}(\operatorname{apply}(S, qprime), \operatorname{apply}(A, a)))$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.effectStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum is the sum of the image subspaces indexed by all and only defined transitions. Repeated targets and loops are allowed. An empty index family contributes the zero submodule.

**Definition 1.5 (The all-state recurrence).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] [\operatorname{DecidableEq}(Q)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), F: \operatorname{Finset}(Q), A: Alphabet \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \forall q: Q, \operatorname{propagation}(M, F, A, U, 0, q) = \operatorname{ite}(q \in F, U, \operatorname{bottom}()) \land \forall n: N, \forall q: Q, \operatorname{propagation}(M, F, A, U, n + 1, q) = \operatorname{effectStep}(M, A, \operatorname{propagation}(M, F, A, U, n), q)$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.propagation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initialization is U exactly at accepting states and zero elsewhere. The next tuple uses the same fixed transition operator, so a simultaneous plateau is a fixed point.

**Theorem 1.6 (Exact accepted-word characterization).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] [\operatorname{DecidableEq}(Q)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), F: \operatorname{Finset}(Q), A: Alphabet \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \forall n: N, \forall q: Q, \operatorname{propagation}(M, F, A, U, n, q) = \operatorname{acceptedSpan}(M, F, A, U, n, q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.propagation_eq_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At horizon zero the only possible word is empty. A nonempty accepted word uniquely separates into its head a, the actual next state qprime, and an accepted tail from qprime. The identity A(aw) = A(a)A(w), submodule map of a span, and induction identify the independent word span with the recurrence at every state and horizon. No extra permission or read is inferred.

**Theorem 1.7 (The simultaneous rank-offset horizon).**

$$\forall K, E, Alphabet, Q: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] [\operatorname{DecidableEq}(Q)] [\operatorname{Fintype}(Q)] [\operatorname{FiniteDimensional}(K, E)] \forall M: \operatorname{BaseAutomaton}(Alphabet, Q), F: \operatorname{Finset}(Q), A: Alphabet \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), (\forall n: N, (\forall q: Q, \operatorname{propagation}(M, F, A, U, n + 1, q) = \operatorname{propagation}(M, F, A, U, n, q)) \Rightarrow \forall m: N, \forall q: Q, \operatorname{propagation}(M, F, A, U, n + m, q) = \operatorname{propagation}(M, F, A, U, n, q)) \land (\forall n: N, \operatorname{card}(Q) \times \operatorname{finrank}(K, E) - \operatorname{card}(F) \times \operatorname{finrank}(K, U) \leq n \Rightarrow \forall q: Q, \operatorname{propagation}(M, F, A, U, n, q) = \operatorname{propagation}(M, F, A, U, \operatorname{card}(Q) \times \operatorname{finrank}(K, E) - \operatorname{card}(F) \times \operatorname{finrank}(K, U), q)) \land \forall q: Q, \operatorname{fullFuture}(M, F, A, U, q) = \operatorname{propagation}(M, F, A, U, \operatorname{card}(Q) \times \operatorname{finrank}(K, E) - \operatorname{card}(F) \times \operatorname{finrank}(K, U), q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.simultaneous_stabilization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Q is finite and E is finite dimensional. Set d = finrank(K,E), r = finrank(K,U), and B = |Q|d - |F|r, using natural subtraction. The rank sum over the actual coordinate subspaces starts at |F|r and is bounded by |Q|d. The existing FiniteSequentialWordCertificate.bounded_monotone_has_equal_step supplies a consecutive equal-rank pair by B. Since every coordinate increases, equality of the sums forces equal rank at every coordinate; inclusion then forces simultaneous subspace equality. Iteration of the same tuple operator preserves that equality. Every accepted word belongs to its own finite-horizon span, hence to the stable tuple, proving fullFuture(q) = propagation(B,q) for every q, including the distinguished start. This uses the sum of coordinate ranks directly; it does not identify that sum with the rank of a correlated lifted space. Empty F or Alphabet, zero U or E, arbitrary loops and partial undefined transitions need no additional hypothesis.

**Definition 1.8 (The actual finite successor chain).**

$$\forall L: N, \operatorname{start}(\operatorname{chain}(L)) = 0 \land \forall q: \operatorname{Fin}(L + 1), \operatorname{step}(\operatorname{chain}(L), q, \operatorname{unit}()) = \operatorname{ite}(\operatorname{val}(q) < L, \operatorname{some}(\operatorname{val}(q) + 1), \operatorname{none}())$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.chain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alphabet is Unit, the states are Fin(L+1), the start has value zero, and only the final state has no successor. The displayed natural successor is regarded as its bounded Fin element.

**Definition 1.9 (Sole terminal acceptance).**

$$\forall L: N, \operatorname{chainFinal}(L) = \{L\}$$

*Formalization.* `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.chainFinal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singleton contains the Fin(L+1) state of value L. It also describes the length-zero chain.

**Theorem 1.10 (Arbitrary initial-state plateaus).**

$$\forall K, E: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall L: N, \forall U: \operatorname{Submodule}(K, E), (\forall n: N, \forall q: \operatorname{Fin}(L + 1), \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, n, q) = \operatorname{ite}(L \leq \operatorname{val}(q) + n, U, \operatorname{bottom}())) \land (\forall n: N, n < L \Rightarrow \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, n, \operatorname{start}(\operatorname{chain}(L))) = \operatorname{bottom}()) \land \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, L, \operatorname{start}(\operatorname{chain}(L))) = U \land 2 \leq L \Rightarrow U \neq \operatorname{bottom}() \Rightarrow (\operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, 1, \operatorname{start}(\operatorname{chain}(L))) = \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, 0, \operatorname{start}(\operatorname{chain}(L))) \land \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, L, \operatorname{start}(\operatorname{chain}(L))) \neq \operatorname{propagation}(\operatorname{chain}(L), \operatorname{chainFinal}(L), \operatorname{constantIdentity}(), U, 0, \operatorname{start}(\operatorname{chain}(L))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.arbitrary_chain_delay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L and every submodule U over any of the stated scalar and carrier choices, put every letter effect equal to identity and accept only the chain terminal. At state q the propagated space is U exactly when L <= q.val+n and is zero otherwise. Induction on n uses the actual successor edge and the absence of an edge from the terminal. Consequently the initial space is zero for every n<L and is U at L. Taking K=R, E=R and U=R gives the scalar delay family, with L=0 and L=1 included. If L>=2 and U is nonzero, the initial spaces at zero and one agree, but the length-L space differs. Thus equality at the initial state alone cannot replace simultaneous equality. Arbitrarily many initial plateaus follow by increasing L. These are algebraic horizon statements; they assert no numerical, physical-resource or cost improvement.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.Accepts`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.acceptedSpan`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.arbitrary_chain_delay`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.chain`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.chainFinal`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.effectStep`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.fullFuture`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.propagation`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.propagation_eq_accepted`
- Truth anchor: `D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.simultaneous_stabilization`
- Dependency: [D5/S0/Automata/TypedPartialDFAO](../../../S0/Automata/TypedPartialDFAO.md)
- Dependency: [D5/S3/Observer/LinearMemory/FiniteWordReachability](FiniteWordReachability.md)
