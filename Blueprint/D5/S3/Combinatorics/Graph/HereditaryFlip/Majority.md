# Majority and flag completion

## Abstract

Hereditary families of finite supports are majority closed exactly when all empty, singleton and pair constraints determine membership. Their pair completion is the least majority-closed containing family.

Let V be any type with decidable equality. Supports are finite subsets of V, and a family K is a set of such supports; V and K need not be finite. Heredity means IsLowerSet K for inclusion of supports. The empty family is allowed. Every nonempty hereditary family contains the empty support.

**Definition 1.1 (Support majority).**

$$\operatorname{majority}\left(A, B, C\right) = \operatorname{union}\left(\operatorname{union}\left(\operatorname{intersection}\left(A, B\right), \operatorname{intersection}\left(B, C\right)\right), \operatorname{intersection}\left(C, A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.majority` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex occurs in the majority exactly when at least two inputs contain it.

**Definition 1.2 (Majority closure).**

$$(\operatorname{MajorityClosed}\left(K\right)) \Leftrightarrow (\forall A \in \operatorname{Finset}\left(V\right),\; \forall B \in \operatorname{Finset}\left(V\right),\; \forall C \in \operatorname{Finset}\left(V\right),\; ((A \in K) \land ((B \in K) \land (C \in K))) \Rightarrow (\operatorname{majority}\left(A, B, C\right) \in K))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.MajorityClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All three inputs and the majority belong to the same family.

**Definition 1.3 (All small faces determine membership).**

$$(\operatorname{Flag}\left(K\right)) \Leftrightarrow (\forall S \in \operatorname{Finset}\left(V\right),\; (\forall T \in \operatorname{Finset}\left(V\right),\; ((T \subseteq S) \land (\operatorname{card}\left(T\right) \le 2)) \Rightarrow (T \in K)) \Rightarrow (S \in K))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.Flag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SmallFaces(K,S) means that every T contained in S with cardinality at most two belongs to K. This includes the empty support and singletons. A vertex whose singleton is absent cannot appear in a completed face.

**Definition 1.4 (Completion from small faces).**

$$\forall S \in \operatorname{Finset}\left(V\right),\; (S \in \operatorname{pairClosure}\left(K\right)) \Leftrightarrow (\forall T \in \operatorname{Finset}\left(V\right),\; ((T \subseteq S) \land (\operatorname{card}\left(T\right) \le 2)) \Rightarrow (T \in K))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.pairClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The completion keeps exactly the finite supports satisfying all original empty, singleton and pair constraints.

**Theorem 1.5 (Hereditary majority closure is flagness).**

$$\forall K \in \operatorname{Set}\left(\operatorname{Finset}\left(V\right)\right),\; (\operatorname{IsLowerSet}\left(K\right)) \Rightarrow ((\operatorname{MajorityClosed}\left(K\right)) \Leftrightarrow (\operatorname{Flag}\left(K\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.majority_closed_iff_flag` (`✓ std3`). ∎

*Citation.* Kassahun H Betre; Yan X Zhang; Carter Edmond (2024). *Pure Simplicial and Clique Complexes with a Fixed Number of Facets*. DOI: [10.48550/arXiv.2411.12945](https://doi.org/10.48550/arXiv.2411.12945). URL: <https://arxiv.org/html/2411.12945v1>.

*Commentary.*

For a hereditary K, majority closure and flagness are equivalent. In a majority, every subset of size at most two is contained in a common supporting input: two subsets of the three input positions, each of size at least two, intersect. Heredity makes that small subset legal, and flagness makes the majority legal. Conversely, use strong induction on a support S satisfying all small constraints. The case of size at most two is immediate. Otherwise choose three distinct vertices a,b,c. The three erased supports are smaller, satisfy the same local constraints and belong to K inductively. Their majority is S. Heredity alone does not guarantee majority closure: the three edges of a triangle belong to its boundary, while their majority is the missing triangle. The finite version is classical; the statement here permits arbitrary ambient types and absent vertices.

**Theorem 1.6 (Least majority-closed extension).**

$$\forall K \in \operatorname{Set}\left(\operatorname{Finset}\left(V\right)\right),\; (\operatorname{IsLowerSet}\left(K\right)) \Rightarrow (\operatorname{IsLeast}\left(\operatorname{majorityClosedExtensions}\left(K\right), \operatorname{pairClosure}\left(K\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.pair_closure_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extensions are all families L with K contained in L and MajorityClosed L. Pair completion contains K, is hereditary and is flag, hence is majority closed. For universal minimality, L is not assumed hereditary. Strong induction on the cardinality of S in pairClosure K starts with S in K for cardinality at most two. In larger cardinalities, the same three erased faces lie in L inductively, and their majority reconstructs S. Thus pairClosure K is contained in every such L. This is a consequence of the small-face induction, with no claim of new mathematical novelty. No graph distance or metric median assertion is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.Flag`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.MajorityClosed`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.majority`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.majority_closed_iff_flag`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.pairClosure`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Majority.pair_closure_is_least`
