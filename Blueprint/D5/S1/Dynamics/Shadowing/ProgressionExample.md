# The Full Progression Example for Question 5.6

## Abstract

A weakly mixing compact metric system with neighborhood two-shadowing and without dense nonempty small periodic sets.

Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, Question 5.6 asks: Is there a weakly mixing system which has the neighborhood N-shadowing property (N>1) that does not have dense small periodic sets? Use the intended nonempty meaning of a small periodic set. The printed definition omits nonemptiness; allowing the empty set would trivialize it. The phase space is X={x in {0,1}^N : for every s>=0,p>=1 some j<=p^2+2 has x(s+jp)=0}, with the genuine first-disagreement metric, and the one-sided left shift sigma. No homeomorphism hypothesis is imposed by the source's compact metric system definition.

The arithmetic-progression construction, constants and rotation deletion method are attributed to Pro.

**Theorem 1.1 (Weak mixing on all nonempty product open sets).**

$$\begin{aligned}\forall ell: \mathbb{N} \to \mathbb{N},\\(\forall p \in \mathbb{N}, 0<p \Rightarrow 3\le\operatorname{ell}(p)) \Rightarrow\\\forall U,V: \operatorname{Set}(\operatorname{ProgressionPoint}(ell)\times \operatorname{ProgressionPoint}(ell)),\\\operatorname{IsOpen}(U) \Rightarrow \operatorname{IsOpen}(V) \Rightarrow \operatorname{Nonempty}(U) \Rightarrow \operatorname{Nonempty}(V) \Rightarrow\\\exists n \in \mathbb{N}, \exists z \in U,\\(\operatorname{iterate}(\operatorname{progressionShift}(ell), n, \operatorname{fst}(z)), \operatorname{iterate}(\operatorname{progressionShift}(ell), n, \operatorname{snd}(z))) \in V\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ProgressionExample.progression_shift_product_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For this generic statement ell is any natural-valued length function satisfying ell(p)>=3 for every positive p. Set(T) denotes subsets of T and iterate(f,n,x) denotes f^[n](x). For arbitrary nonempty open U,V in ProgressionPoint(ell) times ProgressionPoint(ell), choose contained nonempty open rectangles. Apply open-set mixing to each coordinate pair. The maximum of their two thresholds supplies one common hitting time and two points, proving transitivity of the square map.

In the endpoint formula, X is ProgressionPoint(quadraticProgressionLength) and sigma is progressionShift(quadraticProgressionLength). Set(X) denotes all subsets of X; iterate(f,n,x) denotes f^[n](x), sigma^p denotes p-fold iteration, and image(f,B) denotes the direct image. MapsTo(f,B,B) means image(f,B) is a subset of B. NeighborhoodTwoShadowing(sigma) is the existing predicate: for every epsilon>0 there is delta>0 such that every infinite natural-time delta-pseudo-orbit admits one same nonempty finite A in X with card(A)<=2 and initial diameter<epsilon, and at every natural time its distance to the shifted set is <epsilon. The minimizing branch may vary with time.

**Theorem 1.2 (The full compact-system existence conclusion).**

$$\begin{aligned}\operatorname{Nonempty}(X) \land \operatorname{CompactSpace}(X) \land\\\operatorname{Continuous}(sigma) \land \operatorname{Surjective}(sigma) \land\\(\forall U,V: \operatorname{Set}(X\times X), \operatorname{IsOpen}(U) \Rightarrow \operatorname{IsOpen}(V) \Rightarrow \operatorname{Nonempty}(U) \Rightarrow \operatorname{Nonempty}(V) \Rightarrow\\\exists n \in \mathbb{N}, \exists z \in U, (\operatorname{iterate}(sigma, n, \operatorname{fst}(z)), \operatorname{iterate}(sigma, n, \operatorname{snd}(z))) \in V) \land\\\operatorname{NeighborhoodTwoShadowing}(sigma) \land\\\exists U: \operatorname{Set}(X), \operatorname{IsClopen}(U) \land \operatorname{Nonempty}(U) \land\\(\forall p \in \mathbb{N}, 0<p \Rightarrow \forall B: \operatorname{Set}(X), B \subseteq U \Rightarrow\\\operatorname{MapsTo}(sigma^{p}, B, B) \Rightarrow \neg \operatorname{Nonempty}(B)) \land\\\neg (\exists B: \operatorname{Set}(X), \operatorname{Nonempty}(B) \land \operatorname{IsCompact}(B) \land B \subseteq U \land \exists p \in \mathbb{N}, 0<p \land \operatorname{image}(sigma^{p}, B)=B)\end{aligned}$$

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
