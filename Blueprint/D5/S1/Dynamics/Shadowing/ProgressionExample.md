# The Full Progression Example for Question 5.6

## Abstract

A weakly mixing compact metric system with neighborhood two-shadowing and without dense nonempty small periodic sets.

Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, Question 5.6 asks: Is there a weakly mixing system which has the neighborhood N-shadowing property (N>1) that does not have dense small periodic sets? Use the intended nonempty meaning of a small periodic set. The printed definition omits nonemptiness; allowing the empty set would trivialize it. The phase space is X={x in {0,1}^N : for every s>=0,p>=1 some j<=p^2+2 has x(s+jp)=0}, with the genuine first-disagreement metric, and the one-sided left shift sigma. No homeomorphism hypothesis is imposed by the source's compact metric system definition.

The construction, constants and rotation deletion method are attributed to the supplied completed Pro proposal, with isolated ordinary mathematical review. The actual Lean proofs establish the formal conclusion independently of that ordinary approval. Bounded source and library searches do not establish worldwide novelty or priority.

**Theorem 1.1 (Weak mixing on all nonempty product open sets).**

$$\begin{aligned}\forall U, V \subseteq X\times X,\\\operatorname{IsOpen}(U) \land \operatorname{IsOpen}(V) \land \operatorname{Nonempty}(U) \land \operatorname{Nonempty}(V) \Rightarrow\\\exists n, z, z \in U \land (\operatorname{iterate}(sigma, n, \operatorname{fst}(z)), \operatorname{iterate}(sigma, n, \operatorname{snd}(z))) \in V\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionExample.progression_shift_product_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonempty open U,V in X times X, choose contained nonempty open rectangles. Apply open-set mixing to each coordinate pair. The maximum of their two thresholds supplies one common hitting time and two points, proving transitivity of the square map.

**Theorem 1.2 (The full compact-system existence conclusion).**

$$\begin{aligned}\operatorname{Nonempty}(X) \land \operatorname{CompactSpace}(X)\\\operatorname{Continuous}(sigma) \land \operatorname{Surjective}(sigma)\\\operatorname{ProductTransitive}(sigma) \land \operatorname{NeighborhoodTwoShadowing}(sigma)\\\exists U, \operatorname{IsClopen}(U) \land \operatorname{Nonempty}(U) \land \operatorname{NoNonemptyPeriodicSubset}(U)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example` (`✓ std3`). ∎

*Resolves.* `Problems/meddaugh-stephens-2025-mixing-small-periodic-sets` (proved) by `D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meddaugh-stephens-2025-mixing-small-periodic-sets","declaration_gid":"D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The all-zero configuration witnesses nonemptiness, and the closed finite-alphabet carrier is compact. Zero-prepending gives surjectivity, while zero-gap joining gives mixing and hence product transitivity. The exact original neighborhood contract holds with the single fixed N=2 for all accuracies and all infinite natural-time pseudo-orbits. Take U=[1], containing 10-infinity. For every p>0 it contains no nonempty B with sigma^p(B) subset B; hence it contains no nonempty compact B with sigma^p(B)=B. One nonempty open obstruction negates density of nonempty small periodic sets. This is the complete intended existence conclusion, not a finite instance or a conditional mask statement.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ProgressionExample.progression_shift_product_transitive`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example`
- Dependency: [D5/S1/Dynamics/Shadowing/ProgressionTwoShadowing](ProgressionTwoShadowing.md)
