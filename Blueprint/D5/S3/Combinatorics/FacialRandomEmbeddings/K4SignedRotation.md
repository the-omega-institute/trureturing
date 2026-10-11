# K4 Signed Ribbons and the Dyadic Obstruction

## Abstract

For the uniform signed-rotation law on K4, none of the three boundary types has expected count two.

Let Omega be a finite set of equally weighted states, E an event-index set, and T a decidable relation. EventCount(T,e) counts the states omega satisfying T(omega,e). TotalCount(T) counts all incident pairs (omega,e), with the state index summed first. UniformExpectedCount(T) is TotalCount(T) divided by the cardinality of Omega, in the rational numbers. EventTransport(T,phi,e,f) means that T(phi(omega),f) is equivalent to T(omega,e) for every omega. Transport(T,root) means that for every e in E there is a bijection phi of Omega such that T(phi(omega),e) if and only if T(omega,root), for every omega. These are actual event-preserving bijections; equality of marginal probabilities is a conclusion.

**Theorem 1.1 (A State Bijection Preserves Event Cardinality).**

$$\forall Omega \in FiniteType,\; \forall E \in Type,\; \forall T \in \operatorname{DecidableRelation}\left(Omega, E\right),\; \forall e \in E,\; \forall f \in E,\; \forall phi \in \operatorname{Equiv}\left(Omega, Omega\right),\; \operatorname{EventTransport}\left(T, phi, e, f\right) \Rightarrow \operatorname{EventCount}\left(T, e\right) = \operatorname{EventCount}\left(T, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.event_count_eq_of_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindex the finite sum along phi. Its pointwise event equivalence identifies every summand, so the two event counts are equal. The event-index type need not be finite for this step.

**Theorem 1.2 (Double Counting a Transitive Event Family).**

$$\forall Omega \in FiniteType,\; \forall E \in FiniteType,\; \forall T \in \operatorname{DecidableRelation}\left(Omega, E\right),\; \forall root \in E,\; \operatorname{Transport}\left(T, root\right) \Rightarrow \operatorname{TotalCount}\left(T\right) = \operatorname{card}\left(E\right) \cdot \operatorname{EventCount}\left(T, root\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.total_count_eq_card_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Interchange the two finite sums. Every event column has the root event's cardinality, so the total number of incidences is the number of event indices times the root cardinality.

**Theorem 1.3 (The State Count Must Absorb the Denominator).**

$$\forall Omega \in FiniteType,\; \forall E \in FiniteType,\; \forall T \in \operatorname{DecidableRelation}\left(Omega, E\right),\; \forall root \in E,\; \operatorname{Transport}\left(T, root\right) \Rightarrow \left(\forall q \in Nat,\; \left(\operatorname{Nonempty}\left(Omega\right) \land q \ne 0\right) \Rightarrow \left(\operatorname{UniformExpectedCount}\left(T\right) = \frac{\operatorname{card}\left(E\right)}{q} \Rightarrow \operatorname{Divides}\left(q, \operatorname{card}\left(Omega\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.expected_denominator_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty Omega and a chosen root in E, equating the uniform mean with card(E)/q and clearing the nonzero denominators gives q times the root count equal to card(Omega). Thus q divides the state-space cardinality. No primality or coprimality assumption is needed.

**Theorem 1.4 (A Dyadic Sample Space Excludes One Third).**

$$\forall Omega \in FiniteType,\; \forall E \in FiniteType,\; \forall T \in \operatorname{DecidableRelation}\left(Omega, E\right),\; \forall root \in E,\; \operatorname{Transport}\left(T, root\right) \Rightarrow \left(\forall r \in Nat,\; \operatorname{card}\left(Omega\right) = 2^{r} \Rightarrow \operatorname{UniformExpectedCount}\left(T\right) \ne \frac{\operatorname{card}\left(E\right)}{3}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.dyadic_expected_count_ne_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Omega has 2^r elements, a mean of card(E)/3 would force 3 to divide 2^r. Primality of 3 would then force 3 to divide 2, which is impossible. The conclusion concerns the stated uniform finite law; it makes no assertion about nonuniform sampling or a different quotient of the state space.

For K4 the edge order is 01,02,03,12,13,23. Each edge contributes four flags, two sides at its lower endpoint and two at its upper endpoint. Four independently chosen rotation bits select ascending or reversed cyclic neighbour orders; six independent twist bits select band attachments. Thus State is Fin(16) times Fin(64), containing all 1024 outcomes. The corner and band maps are fixed-point-free involutions. The face permutation applies band then corner. Its integer-power cycles are oriented boundary traversals. The two-matching component theorem proves that each combinatorial boundary component consists of two disjoint opposite oriented cycles.

**Theorem 1.5 (The Finite Classifier Has Combinatorial Ribbon Boundary Semantics).**

$$\forall ty \in \operatorname{Fin}\left(3\right),\; \forall s \in State,\; \forall e \in Edge,\; \operatorname{EdgeType}\left(s, e\right) = ty \Leftrightarrow \operatorname{HasType}\left(ty, s, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.classification_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a chosen endpoint, good singular means that the two side flags lie in the same oriented face orbit. Bad singular means that they lie in opposite oriented orbits of the same combinatorial boundary component. Regular means that the two side flags lie in different corner/band components. The finite classifier is proved equivalent to these predicates. Permutation orbits on these 24 flags are determined by the first 24 iterates.

**Definition 1.6 (An Exact Third for Some Physical Edge Type).**

$$claim \Leftrightarrow \left(\exists ty \in \operatorname{Fin}\left(3\right),\; \operatorname{UniformExpectedCount}\left(\operatorname{HasType}\left(ty\right)\right) = \frac{6}{3}\right)$$

*Formalization.* `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This closed claim says that at least one of good singular, bad singular or regular has expected count six divided by three under the uniform law on all 1024 states. Negating this existential excludes each equality, which is stronger within this specified law than negating the conjunction of all three equalities.

**Theorem 1.7 (All Three Exact-Third Equalities Fail Under the Specified Law).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six actual vertex relabellings take edge 01 to every edge. The corresponding state maps are proved bijective. Finite verification of the corner and band intertwinings gives conjugate face permutations, so permutation-orbit transport establishes boundary-classifier equivariance. Applying the finite-event theorem with 1024 = 2^10 excludes mean two for every physical type, without assuming equal marginal probabilities. The law is the independently sampled rotations and signs in the Ghanbari–Šámal public notebook at commit 0d4404941894d3ef8dd9f27f1e61829bec2bcde5. The paper's phrase random embedding does not itself specify a law. This result does not concern uniform unlabelled maps, nonuniform laws, or conditioning on orientability, genus or face count. No resolution of an unspecified-law conjecture, nor any cycle double cover theorem, is asserted. Realization as a closed surface and topological classification are outside this formalization.

## References

- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.claim`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.classification_iff`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.dyadic_expected_count_ne_third`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.event_count_eq_of_equiv`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.expected_denominator_dvd`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.result`
- Truth anchor: `D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.total_count_eq_card_mul`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](../PerfectMatchings/InvolutionOrbitSplit.md)
