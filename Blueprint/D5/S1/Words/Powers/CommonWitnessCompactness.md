# Common Witness Compactness for Finite Word Relations

## Abstract

A globally oriented common witness exists exactly when every finite subrelation has one.

**Theorem 1.1 (Finite character with one global witness orientation).**

$$\forall u \in Universe,\; \forall A \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{CommonWitness}\left(G\right)) \Leftrightarrow (\forall T \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{subset}\left(T, G\right)) \Rightarrow ((\operatorname{Finite}\left(T\right)) \Rightarrow (\operatorname{CommonWitness}\left(T\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite` (`✓ std3`). ∎

*Citation.* C. Aiswarya, Amaldev Manuel, Saina Sunny (2026). *Deciding Conjugacy of a Rational Relation*. URL: <https://arxiv.org/abs/2307.06777v4>.

*Commentary.*

For every universe level u, every alphabet A in Type u, and every set G of literal List A pairs, CommonWitness(G) holds exactly when every finite subset T of G has CommonWitness(T). CommonWitness(G) is the disjunction of one word z satisfying a ++ z = z ++ b for every (a,b) in G, or one word z satisfying z ++ a = b ++ z for every pair in G. The orientation is global for G; each finite T retains its own disjunction.

The statement includes empty and infinite relations, empty words, the neutral pair ([],[]), empty alphabets, infinite alphabets, and arbitrary universe levels. It assumes no Finite, Fintype, DecidableEq or Nonempty structure on A and does not bound witness length. It is a literal List and Set result, with no infinite-word or group-element endpoint.

For the inner orientation, a nonempty first component is selected from G. For a witness z of a ++ z = z ++ b, the word a ++ z has period length(a) and starts with a. Reducing indices modulo this positive period shows that the shorter of two such words is a prefix of the longer; cancelling a gives prefix comparability of the witnesses. Two distinct shared witnesses transport a third row through the cyclic centralizer: residuals commute with the anchor right word, and the cyclic centralizer classification transfers commutation to the row under test. If a row has at most one shared anchor witness, a finite three-row union forces all such unique candidates to agree. Rows with empty first component are neutral by length cancellation. The outer case follows after swapping each pair. For the global disjunction, either every finite subset admits an inner witness, or a finite inner obstruction exists. In the latter case adjoining that obstruction to any finite subset forces an outer witness, so outer finite character applies.

Aiswarya, Manuel and Sunny, arXiv:2307.06777v4, Definition 5, p. 14, and Lemma 6, p. 25, give the finite-alphabet common-witness principle. The cited source is a literature boundary: its finite-alphabet scope is recorded, while the arbitrary-alphabet List statement, the global orientation disjunction and all degenerate cases are proved here.

## References

- Truth anchor: `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite`
- Dependency: [D5/S1/Words/Powers/CyclicCentralizer](CyclicCentralizer.md)
