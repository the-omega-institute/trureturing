# Two-State Short-Word Certificate Width

## Abstract

Original-word certificates for total two-state output automata have linear worst-case width.

**Theorem 1.1 (Finite attained width and the linear sandwich).**

Lean statement: `D5/S0/Automata/TwoStateCertificateWidth.two_state_certificate_width`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/TwoStateCertificateWidth.two_state_certificate_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alphabet is exactly Fin k. A sample is a finite set D of distinct original words, each of length at most two, with a Boolean label on each member. Realizable means that an actual native total deterministic output automaton, with an initial state and at most two states, matches those observations. Every transition and state output is defined. Outside D no output is prescribed. One-state and constant-output machines are included, as are empty samples, the empty word and singleton words.

The predicate Realizable uses a total label function only for convenience. completeLabel extends an arbitrary function on D by false elsewhere; partial_native identifies its realizability with correctness for the original partial labeling. The default outside D has no effect on any restriction. For a realizable sample omega2 is infinity. Otherwise the full sample itself is an obstruction, and well-ordering selects the least cardinality of an unrealizable original-word subset. The theorem supplies an attaining subset and compares it with every other unrealizable subset.

obstructionRange k contains exactly these finite minimum sizes for unrealizable short samples on Fin k. H2 is their supremum in the extended natural numbers. For every k at least six this range is finite and nonempty, its greatest element h is attained, and H2(k)=h. The bounds are floor((k-2)/4) at the lower end and 16(k+1) at the upper end. Natural division expresses this floor because k is at least six.

For the upper estimate, normalize any two-state machine by its Boolean output, handling constant output separately. For each possible initial output, the original branch-core theorem supplies at most 8k+1 observations excluding that branch. Their union contains at most 16k+2 original words, hence at most 16(k+1), and excludes every native two-state machine. Taking the minimum and then the supremum gives the upper bound.

For the lower estimate put m=2n+3. The alphabet Fin m plus Fin m has 2m letters: vertex letters x_i in one summand and query letters e_i in the other. Label the word x_i e_i false and x_next(i) e_i true, with next cyclic. The query letter recovers i; adjacent vertices differ, so these are 2m distinct words and the labels are consistent. In a full model the states reached after adjacent vertex letters must differ, because reading their common query yields opposite outputs. This colors the odd cycle with at most two colors, contradicting its chromatic number three.

Every restriction E of the constructed cycleDomain with at most n original words omits some false-labeled word x_j e_j. Every retained observation here is one of the length-two endpoint/query words x_i e_i or x_next(i) e_i; E may keep only one member of such a query pair, and E may be empty. Cut the cycle at j and transport the path graph's Boolean coloring along the resulting vertex order. A total Boolean-state machine resets each vertex letter to its color. For every query other than e_j, its two color entries give false and true at the required endpoints. The query e_j constantly gives true; its omitted false observation is unrestricted. Thus a single shared total table fits every such retained cycleDomain restriction.

An injective alphabet map induces an injective map of words. Extend each transition table to the larger alphabet using identity transitions on unused letters; the state carrier, initial state and outputs stay fixed. Pulling back a larger-alphabet machine gives the reverse implication. Every raw subset of the image has a unique inverse subset, with equal cardinality and the same restricted labels, and realizability is equivalent in both directions. For k at least six take n=(k-6)/4 and m=2n+3; then 2m is at most k and n+1=floor((k-2)/4). Embedding both letter roles into Fin k gives the lower bound and a nonempty obstruction range. No optimality of either constant, longer-word assertion or larger-state claim is made.

## References

- Truth anchor: `D5/S0/Automata/TwoStateCertificateWidth.two_state_certificate_width`
- Dependency: [D5/S0/Automata/TwoStateShortWordSampleBound](TwoStateShortWordSampleBound.md)
