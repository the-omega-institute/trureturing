# An intersection of parabolics in a two-factor quandle product

## Abstract

Two conjugates of the upper factor in a two-factor quandle product have a nonparabolic intersection.

**Definition 1.1 (The orthogonality relation of an oposet).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \operatorname{Oposet}\left(I\right) : Type$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.Oposet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Definition 2.1 supplements the supplied partial order on I with a symmetric, irreflexive binary relation on I. Orthogonality implies incomparability in both directions. If i ≤ j and j is orthogonal to k, then i is orthogonal to k.

**Definition 1.2 (Indices strictly below a given index).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall k \in I,\; \operatorname{LowerIndex}\left(k\right) = \{i : I \mid i < k\}$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.LowerIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

The subtype uses the strict order of I. Its elements keep the proof that their index is below k.

**Definition 1.3 (The action on the groupoid below an index).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall k \in I,\; \operatorname{LowerAction}\left(G, k\right) : Type$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.LowerAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

A lower action consists of a homomorphism onIndex from G(k) to the permutations of LowerIndex(k). For each b in G(k) and i below k, onFactor gives a multiplicative equivalence from G(i) to G(onIndex(b)(i)), where the underlying index of each subtype element is used. The identity acts as the identity on the dependent disjoint union. Acting by bc equals acting first by c and then by b, as an equality in that union.

**Definition 1.4 (Applying a lower action).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall k \in I,\; \forall A \in \operatorname{LowerAction}\left(G, k\right),\; \forall b \in G\left(k\right),\; \forall i \in \operatorname{LowerIndex}\left(k\right),\; \forall a \in G\left(\operatorname{val}\left(i\right)\right),\; \operatorname{apply}\left(A, b, i, a\right) = (\operatorname{onIndex}\left(A, b, i\right), \operatorname{onFactor}\left(A, b, i, a\right))$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.apply` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Here apply denotes LowerAction.apply. The output is the dependent pair of the permuted lower index and the image of the factor element under onFactor. Its type is the disjoint union indexed by LowerIndex(k).

**Definition 1.5 (Order preservation of a lower action).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall k \in I,\; \forall A \in \operatorname{LowerAction}\left(G, k\right),\; \operatorname{PreservesOrder}\left(A\right) \iff (\forall b \in G\left(k\right),\; \forall i \in \operatorname{LowerIndex}\left(k\right),\; \forall j \in \operatorname{LowerIndex}\left(k\right),\; \operatorname{onIndex}\left(A, b, i\right) \leq \operatorname{onIndex}\left(A, b, j\right) \iff i \leq j)$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.PreservesOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

For each acting element b, the index permutation both preserves and reflects the induced order.

**Definition 1.6 (The three-index quandle law).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall A \in \prod_{k : I} \operatorname{LowerAction}\left(G, k\right),\; \forall ord \in \left(\forall k \in I,\; \operatorname{PreservesOrder}\left(A\left(k\right)\right)\right),\; \operatorname{IsQuandleAction}\left(A, ord\right) \iff (\forall k \in I,\; \forall j \in \operatorname{LowerIndex}\left(k\right),\; \forall i \in \operatorname{LowerIndex}\left(\operatorname{val}\left(j\right)\right),\; \forall a \in G\left(\operatorname{val}\left(i\right)\right),\; \forall b \in G\left(\operatorname{val}\left(j\right)\right),\; \forall c \in G\left(k\right),\; \operatorname{act}\left(A, c, \operatorname{act}\left(A, b, a\right)\right) = \operatorname{act}\left(A, \operatorname{act}\left(A, c, b\right), \operatorname{act}\left(A, c, a\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.IsQuandleAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

The family A includes an action at every index and is supplied with order preservation at every index. For i < j < k and a, b, c in the corresponding factors, c acts on the output of b acting on a. On the other side, c acts on both b and a, and the resulting element from b acts on the resulting element from a. Order preservation at k gives the required strict inequality between their image indices. The equality compares the two dependent pairs in the disjoint union over I.

**Definition 1.7 (A quandle system with nontrivial factors).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \operatorname{QuandleSystem}\left(I, G\right) : Type$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.QuandleSystem` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Definition 2.4 combines an oposet on I with one lower action at each index for the supplied family of groups. Every index permutation preserves and reflects order and orthogonality. The actions satisfy the three-index quandle law. Each factor is nontrivial by the convention on p. 9.

**Definition 1.8 (The relators in the indexed free product).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \operatorname{relators}\left(S\right) = \{r : \operatorname{FreeProduct}\left(G\right) \mid \exists i \in I,\; \exists j \in I,\; \exists a \in G\left(i\right),\; \exists b \in G\left(j\right),\; ((\operatorname{Orthogonal}\left(S, i, j\right) \land r = \operatorname{u}\left(i, a\right) \operatorname{u}\left(j, b\right) (\operatorname{u}\left(j, b\right) \operatorname{u}\left(i, a\right))^{-1}) \lor (i < j \land r = \operatorname{u}\left(i, a\right) \operatorname{u}\left(j, b\right) (\operatorname{u}\left(j, b\right) \operatorname{w}\left(S, b, i, a\right))^{-1}))\}$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.relators` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

The map u(i,a) is the free-product inclusion of a from G(i). The term w(S,b,i,a) is the free-product image of the dependent pair obtained when b acts on a at the strictly lower index i. Each relation contributes its left-hand side times the inverse of its right-hand side.

**Definition 1.9 (The normal-closure quotient).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \operatorname{Q}\left(S\right) = \operatorname{FreeProduct}\left(G\right)/\operatorname{normalClosure}\left(\operatorname{relators}\left(S\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.QuandleProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Definition 2.4 imposes the orthogonal commutations and twists by quotienting the indexed free product by the normal closure of the full relator set.

**Definition 1.10 (The maps of the factors into the quotient).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \forall i \in I,\; \forall a \in G\left(i\right),\; \operatorname{factor}\left(S, i, a\right) = \operatorname{quotientMap}\left(\operatorname{u}\left(i, a\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.factor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

For each i this group homomorphism composes the free-product inclusion with the quotient map for the normal closure of relators(S).

**Definition 1.11 (Subgroups generated by factor images).**

$$\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \forall J \in \operatorname{Set}\left(I\right),\; \operatorname{P}\left(S, J\right) = \operatorname{closure}\left(\{q : \operatorname{Q}\left(S\right) \mid \exists j \in I,\; j \in J \land (\exists a \in G\left(j\right),\; \operatorname{factor}\left(S, j, a\right) = q)\}\right)$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.standardParabolic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Definition 2.13 uses subgroup closure in the actual quotient. The subset J ranges over all subsets of I. A parabolic is the image of this subgroup under conjugation by an element of the quotient.

**Definition 1.12 (The universal affirmative answer).**

$$claim = (\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \forall J \in \operatorname{Set}\left(I\right),\; \forall L \in \operatorname{Set}\left(I\right),\; \forall g \in \operatorname{Q}\left(S\right),\; \forall h \in \operatorname{Q}\left(S\right),\; \exists T \in \operatorname{Set}\left(I\right),\; \exists k \in \operatorname{Q}\left(S\right),\; \operatorname{intersection}\left(g \operatorname{P}\left(S, J\right) (g)^{-1}, h \operatorname{P}\left(S, L\right) (h)^{-1}\right) = k \operatorname{P}\left(S, T\right) (k)^{-1})$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.claim` (`✓ std3`).

*Citation.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Question 9.4 on printed p. 47 asks “In a quandle product, is the intersection between two arbitrary parabolic subgroups again a parabolic subgroup?” Both conjugators are arbitrary elements of Q(S), and all three factor subsets may be any subsets of I. The group and order assumptions are those of the supplied system. Type denotes Lean Type.

**Theorem 1.13 (The intersection need not be parabolic).**

$$\neg (\forall I \in Type,\; [\operatorname{PartialOrder}\left(I\right)], \forall G \in I \to Type,\; [\forall i \in I,\; \operatorname{Group}\left(G\left(i\right)\right)], \forall S \in \operatorname{QuandleSystem}\left(I, G\right),\; \forall J \in \operatorname{Set}\left(I\right),\; \forall L \in \operatorname{Set}\left(I\right),\; \forall g \in \operatorname{Q}\left(S\right),\; \forall h \in \operatorname{Q}\left(S\right),\; \exists T \in \operatorname{Set}\left(I\right),\; \exists k \in \operatorname{Q}\left(S\right),\; \operatorname{intersection}\left(g \operatorname{P}\left(S, J\right) (g)^{-1}, h \operatorname{P}\left(S, L\right) (h)^{-1}\right) = k \operatorname{P}\left(S, T\right) (k)^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.result` (`✓ std3`). ∎

*Resolves.* `Problems/genevois2505q94` (refuted) by `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"genevois2505q94","declaration_gid":"D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anthony Genevois (2025). *Beyond graph products and cactus groups: quandle products of groups*. DOI: [10.48550/arXiv.2505.09194](https://doi.org/10.48550/arXiv.2505.09194). URL: <https://arxiv.org/abs/2505.09194v1>.

*Commentary.*

Take a two-element chain with empty orthogonality as in Example 2.6. Use C16 below C4. The element of C4 with additive coordinate j acts on C16 by multiplication by 13 to the power j. Write a and t for the factor images of the two generators and H for the upper-factor subgroup. The twist in the actual quotient makes a² commute with t², so t² is in both H and its conjugate by a².

The factor inclusions into the semidirect group with forward multiplier 5 satisfy the presentation and give a map from the actual quotient. Comparing the two coordinates of an intersection element in this group excludes odd upper exponents. The identity and t² realize the two even exponents in the source intersection. Its image in C4 is therefore exactly the subgroup with residues 0 and 2.

Conjugation acts trivially on the projection to C4. The image of a standard parabolic is the full C4 if its subset contains the upper index and is trivial otherwise. This rules out every parabolic as the intersection.

## References

- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.IsQuandleAction`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.LowerAction`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.LowerIndex`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.Oposet`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.PreservesOrder`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.QuandleProduct`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.QuandleSystem`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.apply`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.claim`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.factor`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.relators`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.result`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/GenevoisQ94Settlement.standardParabolic`
- Dependency: [D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation](TaThreeInvariantRefutation.md)
