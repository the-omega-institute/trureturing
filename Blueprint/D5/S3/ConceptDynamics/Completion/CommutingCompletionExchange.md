# Commuting Completion Exchange

## Abstract

Commuting predictive completions exchange order and equal completion by all words.

**Lemma 1.1 (The projection kernel is the congruence kernel).**

$$\forall X, O: \operatorname{Type}, F: X \to X, q: X \to O,\\{}readoutRelation(predictiveProjection(F, q)) = congruenceKernel(F, readoutRelation(q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.predictive_projection_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completed readout is the canonical quotient projection from the original state type. Equality of two quotient classes is exactly membership in the predictive setoid relation.

Quotient exactness and soundness therefore identify its readout kernel with the existing congruenceKernel construction. This bridge lets a completed interface be supplied to a second completion.

**Lemma 1.2 (Canonical normal words act by two iterates).**

$$\forall X: \operatorname{Type}, F, G: X \to X, n, m: Nat,\\{}wordAction(F, G, normalWord(n, m)) = iterate(F, n) \circ iterate(G, m).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.normal_word_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normal word consists of n first-generator letters followed by m second-generator letters. Direct induction evaluates its action as the composite of the corresponding iterates.

No commutativity assumption is needed for this representability half, and the proof includes the empty word at n = m = 0.

**Lemma 1.3 (Commuting words have two-block normal forms).**

$$\begin{gathered}\forall X: \operatorname{Type}, F, G: X \to X,\\{}Commute(F, G) \Rightarrow \forall w: List(Bool),\\{}\exists n, m: Nat, wordAction(F, G, w) = iterate(F, n) \circ iterate(G, m).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.word_action_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated monoid is represented explicitly by List Bool, the free word carrier on two named generators. Thus the all-word readout does not assume a normal form in its definition.

Induction on a word counts its two kinds of letters implicitly. A first letter extends the first iterate, while a second letter commutes past the current first iterate using Mathlib's iterate_left law.

**Theorem 1.4 (Commuting completions exchange and equal all words).**

$$\forall X \in \operatorname{Type}, O \in \operatorname{Type}, F \in X \to X, G \in X \to X, q \in X \to O,\; Commute(F, G) \Rightarrow \left(KernelEquivalent(C(F, C(G, q)), C(G, C(F, q))) \land KernelEquivalent(C(G, C(F, q)), C(Generated(F, G), q))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commuting_completion_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

KernelEquivalent means literal equality of readout kernel relations. This is the source theorem's mutual-refinement meaning of the equivalence sign, without claiming equality of quotient types.

The projection-kernel bridge expands the two completion orders into the two nested congruence kernels. Commuting iterates exchange their indices pointwise, proving equality of those kernels.

Word normalization sends every generated word to a pair of iterates, while the canonical normal word realizes every pair. Hence the nested kernel is exactly the kernel of the all-word readout.

No finiteness, inhabitedness, decidable equality, or output structure is assumed. Empty and singleton states, identity and constant maps, and the zero-iterate word are checked in the Lean module.

**Lemma 1.5 (Commutativity cannot be deleted).**

$$\neg Commute(counterexampleF, counterexampleG) \land \neg KernelEquivalent(C(counterexampleF, C(counterexampleG, counterexampleReadout)), C(counterexampleG, C(counterexampleF, counterexampleReadout))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commutativity_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete four-state system distinguishes the two orders. States a and b agree after every G-iterate following every F-iterate, but F after one G-step sends them to differently read states.

The two completion kernels are therefore unequal. This proves that the commutativity premise is necessary for the theorem as a uniform statement, rather than merely recording a proof dependency.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commutativity_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commuting_completion_exchange`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.normal_word_action`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.predictive_projection_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.word_action_normal_form`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient](../Sufficiency/MinimalPredictiveCompletionQuotient.md)
