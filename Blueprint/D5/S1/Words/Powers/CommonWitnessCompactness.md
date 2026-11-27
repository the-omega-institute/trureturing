# Common Witness Compactness for Finite Word Relations

## Abstract

A globally oriented common witness exists exactly when every subrelation of at most three rows has one.

**Theorem 1.1 (Finite character with one global witness orientation).**

$$\forall u \in Universe,\; \forall A \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{CommonWitness}\left(G\right)) \Leftrightarrow (\forall T \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{subset}\left(T, G\right)) \Rightarrow ((\operatorname{Finite}\left(T\right)) \Rightarrow (\operatorname{CommonWitness}\left(T\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite` (`✓ std3`). ∎

*Citation.* C. Aiswarya, Amaldev Manuel, Saina Sunny (2026). *Deciding Conjugacy of a Rational Relation*. URL: <https://arxiv.org/abs/2307.06777v4>.

*Commentary.*

For every universe level u, every alphabet A in Type u, and every set G of literal List A pairs, CommonWitness(G) holds exactly when every finite subset T of G has CommonWitness(T). CommonWitness(G) is the disjunction of one word z satisfying a ++ z = z ++ b for every (a,b) in G, or one word z satisfying z ++ a = b ++ z for every pair in G. The orientation is global for G; each finite T retains its own disjunction.

The statement includes empty and infinite relations, empty words, the neutral pair ([],[]), empty alphabets, infinite alphabets, and arbitrary universe levels. It assumes no Finite, Fintype, DecidableEq or Nonempty structure on A and does not bound witness length. It is a literal List and Set result, with no infinite-word or group-element endpoint.

For the inner orientation, a nonempty first component is selected from G. For a witness z of a ++ z = z ++ b, the word a ++ z has period length(a) and starts with a. Reducing indices modulo this positive period shows that the shorter of two such words is a prefix of the longer; cancelling a gives prefix comparability of the witnesses. Two distinct shared witnesses transport a third row through the cyclic centralizer: residuals commute with the anchor right word, and the cyclic centralizer classification transfers commutation to the row under test. If a row has at most one shared anchor witness, a finite three-row union forces all such unique candidates to agree. Rows with empty first component are neutral by length cancellation. The outer case follows after swapping each pair. For the global disjunction, either every finite subset admits an inner witness, or a finite inner obstruction exists. In the latter case adjoining that obstruction to any finite subset forces an outer witness, so outer finite character applies.

Aiswarya, Manuel and Sunny, arXiv:2307.06777v4, Definition 5, p. 14, and Lemma 6, p. 25, give the finite-alphabet common-witness principle. The cited source is a literature boundary: its finite-alphabet scope is recorded, while the arbitrary-alphabet List statement, the global orientation disjunction and all degenerate cases are proved here.

**Theorem 1.2 (Three rows determine a common signed word).**

$$\forall u \in Universe,\; \forall A \in \operatorname{Type}\left(u\right),\; \forall G \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{CommonWitness}\left(G\right)) \Leftrightarrow (\forall T \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{List}\left(A\right), \operatorname{List}\left(A\right)\right)\right),\; (\operatorname{subset}\left(T, G\right)) \Rightarrow ((\operatorname{Finite}\left(T\right)) \Rightarrow ((\operatorname{ncard}\left(T\right) \le 3) \Rightarrow (\operatorname{CommonWitness}\left(T\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe u, alphabet A in Type u and relation G of List A pairs, CommonWitness(G) holds if and only if CommonWitness(T) holds for every finite subset T of G with ncard(T) at most three. Each T chooses its own word and orientation. The conclusion chooses one finite word and one orientation for all of G. There is no length bound, and G and A may be empty, finite or infinite.

Represent an inner word x by a left tag and an outer nonempty word y by a right tag. The empty outer word has the same equations as the empty inner word, so it receives the latter representation. Fix a row (a,b) with a nonempty. Two distinct common inner words for this row and another row transport every anchor inner word by the cyclic-centralizer argument. If x is inner and y is outer, x ++ y ++ x is inner. Cancelling the two copies of x recovers the outer equation, so two inner words transport every signed anchor word. Swapping the row components proves the same assertion for two outer words. For mixed signs the inner words x and x ++ y ++ x are distinct, since equality would force the nonempty y to have length zero. Thus two distinct shared signed words always transport every signed anchor word.

The signed words shared by the anchor and any row form a nonempty set, by the two-row hypothesis. If this set contains two distinct elements, it contains every anchor word. If all rows have this property, any anchor word works globally. Otherwise choose a row whose shared set is a singleton. Every triple containing the anchor, this row and an arbitrary third row forces that same singleton word, which therefore works globally. Repeated rows are allowed: inserting three rows gives a finite set of cardinality at most three. If no first component is nonempty, singleton solvability and length cancellation force every second component to be empty; the empty inner word then works.

The three-row bound is the result stated here. Definition 5, Proposition 13 and Lemma 6 of the cited paper supply the common-witness terminology and related rigidity and finite-character structure; the three-row bound is not attributed to that source. No claim of literature novelty or sharpness of the bound is made.

## References

- Truth anchor: `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_finite`
- Truth anchor: `D5/S1/Words/Powers/CommonWitnessCompactness.commonWitness_iff_three`
- Dependency: [D5/S1/Words/Powers/CyclicCentralizer](CyclicCentralizer.md)
