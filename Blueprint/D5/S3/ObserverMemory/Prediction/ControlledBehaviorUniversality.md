# Controlled Behavior Universality

## Abstract

Every exact controlled representation maps from its actual image uniquely onto the behavior quotient.

## Local observation and choices

For an event set E(o), its dependency support consists of events below some member of E(o). Intersecting a configuration with that support defines its local record. If equal local records give equal output q, realized-image factorization gives a unique decoder of q from those records. Composing q with any fixed choice map to sets of alphabet symbols preserves this locality. This implication uses the stated locality assumption; the event order alone does not impose it.

## Arbitrary-output quotients on all words

Let L be a prefix-closed language over an arbitrary alphabet and let q map legal words to an arbitrary output set Y. Extend q to every word by adjoining an illegal value, represented by Option(Y). The carrier of the quotient is the whole word space, including illegal words. Two words are equivalent when every continuation produces equal extended output.

The response profile is v maps to extended-q(wv). Equality of profiles is a kernel equivalence. Appending one letter preserves it because a continuation after that letter is itself a continuation of the original word. Quotient.map therefore defines the update on every class, and evaluation of the lifted profile at the empty word defines current output. Prefix closure implies that every extension of an illegal word remains illegal, so any illegal words have the same profile and appending a letter preserves their class.

For any deterministic state machine with a current-state decoder that gives the extended output on every word, equal reached states give equal states after every continuation. The DFA evaluation law for appended words then proves equality of all future outputs. Thus its state kernel refines the response equivalence. No finite-state assumption is needed for this minimality implication. The finite-carrier universal theorem in this module is a separate specialization; it is not needed to make updates on the all-word quotient total.

The language-valued predecessor is the Myhill-Nerode relation on all words recalled on page one of Kozen, On the Myhill-Nerode Theorem for Trees. Equality of arbitrary output profiles replaces equality of Boolean membership; the concatenation argument is unchanged.

## Arbitrary states and the actual representation image

Take a nonempty state carrier X, an arbitrary input alphabet Sigma, arbitrary outputs Y, total deterministic updates F_a : X -> X, and a readout o : X -> Y. The carriers X : Type u, Sigma : Type v, Y : Type w, and an ambient representation carrier S : Type s have independent universes. In this module's notation the state parameter Y is X, the input parameter U is Sigma, and the output parameter O is Y. Every state x is compared; no designated initial state or reachable subset is substituted for X.

Write F_empty = id and F_word = runWord F word. Then B(x)(word) = o(F_word(x)) is controlledBehavior F o. Concatenation is chronological: F_(uv) = F_v composed with F_u, so u is read before v. The identity-readout specialization of `D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.behavior_update_well_defined` supplies this order through its word-action law, evaluated at the empty word.

Let R be equality of B, and let Phi(T) consist of pairs with equal current readouts whose F_a successors belong to T for every a. Thus Phi(T) is ker(o) intersected with all one-step inverse images of T. The public results `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_limit_eq_gfp` and `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_limit_is_greatest_stable_equivalence` identify R with the greatest fixed point of Phi and the greatest equivalence inside ker(o) preserved by every F_a. Neither result requires a finite carrier. Greatest refers to inclusion of relations; it gives the coarsest exact quotient.

Those two suppliers share an input/output universe. To apply them without relating v and w, use inputs ULift.{w} Sigma and outputs ULift.{v} Y, with lifted update F^+(a)(x) = F(a.down)(x) and lifted readout o^+(x) = ULift.up(o(x)). Their behavior kernel equals the original kernel: apply `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_least` in both directions to the original and lifted behavior profiles, using empty-word evaluation for readout refinement and the one-letter profile equation for closure. The resulting factorizations give both kernel inclusions. ULift.up and ULift.down also identify the refinement operators and stable-equivalence families, transporting both conclusions back to the independent original universes.

The quotient Q = X/R is ControlledCompletion F o. Its surjective projection pi, updates Fbar_a, and readout obar_Q are completionProjection, completionUpdate, and completionReadout from this module. They satisfy pi composed with F_a = Fbar_a composed with pi and o = obar_Q composed with pi. By `D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent.controlled_completion_update_and_readout_descend` each commuting quotient update equals Fbar_a and each commuting quotient readout equals obar_Q. This characterizes the unique descended maps on all of Q.

For any r : X -> S, corestrict to Sr = Set.range r with rho = Set.rangeFactorization r. An exact representation consists of arbitrary maps G_a : Sr -> Sr and obar : Sr -> Y satisfying rho composed with F_a = G_a composed with rho for every a, and o = obar composed with rho. Only the actual image Sr carries these maps; no extension of G or obar to unused elements of S is required.

The update squares make the fibers of rho intervention-closed, and the readout square makes rho refine o. Applying dynamic_closure_is_least to this candidate factors B through rho, hence ker(rho) is contained in ker(B). The existing supplier owns the word-induction argument. Mathlib's Setoid.quotientKerEquivOfSurjective identifies X/ker(rho) with Sr. Compose its inverse with Quotient.map id for that kernel inclusion to obtain p : Sr -> Q, characterized by p(rho(x)) = pi(x).

This p is surjective because pi is surjective. It satisfies all three factor equations: pi = p composed with rho; p composed with G_a = Fbar_a composed with p for every a; and obar_Q composed with p = obar. To check the update and readout equations at any z in Sr, write z = rho(x) using surjectivity of rho and apply the corresponding representation square. The same substitution shows that any other factor with the projection equation agrees with p everywhere. Thus there is a unique surjection satisfying the projection, every update, and the readout equations.

If Q is finite, surjectivity gives the lower bound on actual states even when Sr is infinite. Across the independent universes its precise form is Cardinal.lift.{s}(Cardinal.mk Q) <= Cardinal.lift.{u}(Cardinal.mk Sr), using Function.Embedding.ofSurjective and Cardinal.lift_mk_le'. Finiteness of Q alone does not make Sr finite. If encode : Sr -> (Fin b -> Bool) is injective, the encoding does make Sr finite; surjectivity of p and injectivity of encode then give Nat.card Q <= 2^b by Fintype.card_le_of_surjective, Fintype.card_le_of_injective, and the cardinality of functions from Fin b to Bool.

This is an application of the cited existing results. The named theorem controlled_behavior_universal_property described below separately assumes finite source and realized carriers; it is not the supplier of the unrestricted application. Here X, Sigma, Y, and S have no finiteness assumption. The counting conclusion concerns exact representations; a physical b-bit interpretation requires an injective encoding of their complete actual states. It asserts neither an efficient construction nor a time bound, and supplies no literature-priority claim.

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

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_least`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_limit_eq_gfp`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.controlled_limit_is_greatest_stable_equivalence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlledBehavior`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.controlled_behavior_universal_property`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.behavior_update_well_defined`
- Truth anchor: `D5/S3/ObserverMemory/RefinementDescent/ControlledCompletionDescent.controlled_completion_update_and_readout_descend`
