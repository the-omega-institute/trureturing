# Controlled Signature Stabilization

## Abstract

Recursive controlled signatures stabilize at the complete behavior quotient.

**Theorem 1.1 (Controlled signatures compute the complete behavior quotient).**

$$\begin{gathered}\forall Y, U, O,\\\operatorname{FiniteNonempty}(Y), \operatorname{FiniteNonempty}(U), \operatorname{FiniteNonempty}(O),\\F: U \to Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\(\forall m\in \mathbb{N}, \forall y, y', \operatorname{c}(m, y) = \operatorname{c}(m, y') \iff \forall w\in \operatorname{Words}(U), \operatorname{length}(w) \leq m \Rightarrow \operatorname{readoutAfter}(F, q, w, y) = \operatorname{readoutAfter}(F, q, w, y')) \land\\(\forall y, y', \operatorname{c}(m_{*}, y) = \operatorname{c}(m_{*}, y') \iff B(y) = B(y')) \land\\(\forall r\in \mathbb{N}, \forall y, y', \operatorname{c}(m_{*}+r, y) = \operatorname{c}(m_{*}+r, y') \iff \operatorname{c}(m_{*}, y) = \operatorname{c}(m_{*}, y')) \land\\(\forall m\in \mathbb{N}, \operatorname{CompleteAt}(m) \Rightarrow m_{*} \leq m) \land\\(\exists e: \operatorname{SignatureQuotient}(m_{*}) \equiv Z, \forall y\in Y, e(\operatorname{signatureClass}(m_{*}, y)) = \operatorname{behaviorClass}(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization.controlled_signature_algorithm_correctness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty state, input, and readout carriers, let q be a surjective current readout. The depth-zero label is q itself. Each next label consists of q together with the preceding label of every input successor, so the algorithm is constructed directly from the controlled transitions and readout.

At every depth m, equality of recursive labels is equivalent to equal readout after every input word of length at most m. Finiteness of the state carrier supplies a common bound for distinguishing words, and the least complete depth is selected from that bound.

At this least depth, label equality is complete controlled-behavior equality and remains unchanged at every later round. Quotient congruence then gives a canonical equivalence from the stabilized label quotient to the complete controlled behavior quotient, commuting with the two canonical projections.

Repository search found the exact controlled-word semantics in ControlledBehaviorUniversality and a related one-update finite separation argument in FiniteFutureCongruence, but no controlled signature stabilization theorem. Pinned Mathlib supplied Function.ne_iff, Finset.le_sup, Nat.find_spec, Nat.find_min', and Quotient.congrRight, all applied in the proof.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledSignatureStabilization.controlled_signature_algorithm_correctness`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
