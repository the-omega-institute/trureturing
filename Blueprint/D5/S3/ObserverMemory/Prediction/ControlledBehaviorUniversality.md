# Controlled Behavior Universality

## Abstract

Every finite controlled realization maps uniquely onto the complete behavior quotient.

## Local observation and choices

For an event set E(o), its dependency support consists of events below some member of E(o). Intersecting a configuration with that support defines its local record. If equal local records give equal output q, realized-image factorization gives a unique decoder of q from those records. Composing q with any fixed choice map to sets of alphabet symbols preserves this locality. This implication uses the stated locality assumption; the event order alone does not impose it.

## Arbitrary-output quotients on all words

Let L be a prefix-closed language over an arbitrary alphabet and let q map legal words to an arbitrary output set Y. Extend q to every word by adjoining an illegal value, represented by Option(Y). The carrier of the quotient is the whole word space, including illegal words. Two words are equivalent when every continuation produces equal extended output.

The response profile is v maps to extended-q(wv). Equality of profiles is a kernel equivalence. Appending one letter preserves it because a continuation after that letter is itself a continuation of the original word. Quotient.map therefore defines the update on every class, and evaluation of the lifted profile at the empty word defines current output. Prefix closure implies that every extension of an illegal word remains illegal, so any illegal words have the same profile and appending a letter preserves their class.

For any deterministic state machine with a current-state decoder that gives the extended output on every word, equal reached states give equal states after every continuation. The DFA evaluation law for appended words then proves equality of all future outputs. Thus its state kernel refines the response equivalence. No finite-state assumption is needed for this minimality implication. The finite-carrier universal theorem in this module is a separate specialization; it is not needed to make updates on the all-word quotient total.

The language-valued predecessor is the Myhill-Nerode relation on all words recalled on page one of Kozen, On the Myhill-Nerode Theorem for Trees. Equality of arbitrary output profiles replaces equality of Boolean membership; the concatenation argument is unchanged.

## Exact clocks require corresponding state capacity

For a nonempty alphabet choose a letter a. The words consisting of zero through N copies of a have distinct exact lengths. In state_lower_bound_of_distinguishing_family, use these N+1 prefixes and the empty continuation for every pair. Any state decoder correct for length on this domain therefore needs at least N+1 states. Encoding these states in b fixed bits requires b at least the ceiling of log base two of N+1.

If the language contains words of unbounded length, exact length output requires infinitely many distinguishable states. For the full word language over a nonempty alphabet, apply the preceding bound with N equal to the purported finite state count. An empty alphabet or a bounded-length domain does not have this obstruction. Any clock register, external memory, or other interface used by the decoder is part of its state for this counting argument.

**Definition 1.1 (Controlled behavior records every finite-word readout).**

$$\begin{gathered}\forall U, Y, O: \operatorname{Type},\\{}update: U \to \left(Y \to Y\right), readout: Y \to O, y: Y,\\{}\forall word: \operatorname{List}\left(U\right), \operatorname{controlledBehavior}\left(update, readout, y, word\right) = readout(\operatorname{runWord}\left(update, word, y\right)).\end{gathered}$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlledBehavior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an input-indexed update, a readout, an initial state y, and every finite input word, controlledBehavior returns the readout of the state obtained by applying that word from left to right.

**Theorem 1.2 (Controlled behavior has a universal minimal realization).**

$$\begin{gathered}\forall Y, U, O, W,\\{}[\operatorname{Fintype}(Y)], [\operatorname{Fintype}(W)],\\F: U \to \left(Y \to Y\right), q: Y \to O,\\r: Y \to W, G: U \to \left(W \to W\right), o: W \to O,\\\operatorname{Surjective}\left(r\right) \Rightarrow (\forall u\in U, r \circ F(u) = G(u) \circ r) \Rightarrow q = o \circ r \Rightarrow\\(\exists! h: W \to Z, \operatorname{Surjective}\left(h\right) \land \pi = h \circ r \land\\(\forall u\in U, h \circ G(u) = \overline{F}(u) \circ h) \land\\\overline{q} \circ h = o) \land \operatorname{card}(Z) \leq \operatorname{card}(W).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlled_behavior_universal_property` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite controlled state carrier with input-indexed updates and readout q. Let Z be the quotient by equality of every readout after every finite input word. Its projection, induced updates, and induced readout are defined directly from that behavior kernel.

For any finite realization W reached surjectively from Y, commuting with every update and with the readout, there is a unique surjective factor h from W to Z. It factors the canonical projection, intertwines every realized update, and preserves the readout. Surjectivity gives card(Z) at most card(W).

The factor is built from a right inverse of the realization map. Commutation along input words proves that different chosen preimages have equal complete behavior. Surjectivity of the canonical quotient projection proves surjectivity of h, while surjectivity onto W proves all equations and uniqueness pointwise.

The quotient-to-range equivalence identifies a behavior class with its realized response profile. The cardinal inequality follows from surjectivity of the factor, independently of how the states are named.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlledBehavior`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlled_behavior_universal_property`
