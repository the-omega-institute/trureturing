# Small Doubling in the Klein Bottle Group

## Abstract

Two explicit three-element subsets of the Klein bottle group contradict all three small-doubling conjectures printed in section 6.

**Definition 1.1 (The coordinate group).**

$$KleinBottleGroup = \{r: \mathbb{Z}, n: \mathbb{Z}\}$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.KleinBottleGroup` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

The carrier consists of integer pairs. It is the paper's Z semidirect Z at q = -1, the Klein bottle group BS(1,-1).

**Definition 1.2 (The printed coordinate law).**

$$(\forall a \in KleinBottleGroup,\; \forall b \in KleinBottleGroup,\; a \cdot b = ((a).r + \left(-1\right)^{(a).n} \cdot (b).r, (a).n + (b).n)) \land ((1 = (0, 0)) \land (\forall a \in KleinBottleGroup,\; a^{-1} = (-\left(\left(-1\right)^{(a).n} \cdot (a).r\right), -(a).n)))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.instGroupKleinBottleGroup` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

Multiplication is (r,n)(s,m) = (r + (-1)^n s,n+m), the identity is (0,0), and the inverse of (r,n) is (-(-1)^n r,-n).

**Definition 1.3 (Torsion freeness).**

$$\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{IsTorsionFreeGroup}\left(G\right)) \Leftrightarrow (\forall g \in G,\; (g \ne 1) \Rightarrow (\neg \operatorname{IsOfFinOrder}\left(g\right))))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.IsTorsionFreeGroup` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

A group is torsion-free when every nonidentity element has infinite order. Equivalently, no nonidentity element satisfies IsOfFinOrder.

**Definition 1.4 (Abelian subsets).**

$$\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \Rightarrow (\forall X \in \operatorname{Set}\left(G\right),\; (\operatorname{IsAbelianSet}\left(X\right)) \Leftrightarrow (\forall a \in G,\; (a \in Subgroup.closure\left(X\right)) \Rightarrow (\forall b \in G,\; (b \in Subgroup.closure\left(X\right)) \Rightarrow (a \cdot b = b \cdot a))))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.IsAbelianSet` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

The paper states: "A set S is said to be abelian if ⟨S⟩ is an abelian subgroup of G." Subgroup.closure is the generated subgroup.

**Definition 1.5 (Conjecture 6.3).**

$$(claim63) \Leftrightarrow (\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{DecidableEq}\left(G\right)) \Rightarrow ((\operatorname{IsTorsionFreeGroup}\left(G\right)) \Rightarrow (\forall S \in \operatorname{Finset}\left(G\right),\; (Finset.card\left(S\right) \ge 3) \Rightarrow ((1 \in S) \Rightarrow ((Finset.card\left(S \cdot S\right) \le 3 \cdot Finset.card\left(S\right) - 3) \Rightarrow (\operatorname{IsAbelianSet}\left((S : \operatorname{Set}\left(G\right))\right))))))))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim63` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

The paper states: "Conjecture 6.3. Let S be a nonempty finite subset of a torsion-free group G with |S| ≥ 3 and e ∈ S. If |S²| ≤ 3|S| − 3, then ⟨S⟩ is an abelian subgroup of G." Finsets supply finiteness; the cardinality premise also supplies nonemptiness. DecidableEq is implementation structure, classically available for every type.

**Definition 1.6 (Conjecture 6.1).**

$$(claim61) \Leftrightarrow (\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{DecidableEq}\left(G\right)) \Rightarrow ((\operatorname{IsTorsionFreeGroup}\left(G\right)) \Rightarrow (\forall S \in \operatorname{Finset}\left(G\right), A \in \operatorname{Finset}\left(G\right), B \in \operatorname{Finset}\left(G\right),\; (\operatorname{Nonempty}\left(S\right)) \Rightarrow ((S = A \cup B) \Rightarrow ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{IsAbelianSet}\left((A : \operatorname{Set}\left(G\right))\right)) \Rightarrow ((\operatorname{IsAbelianSet}\left((B : \operatorname{Set}\left(G\right))\right)) \Rightarrow ((Finset.card\left(S \cdot S\right) \le 3 \cdot Finset.card\left(S\right) - 3) \Rightarrow (\operatorname{IsAbelianSet}\left((S : \operatorname{Set}\left(G\right))\right)))))))))))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim61` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

The paper states: "Conjecture 6.1. Let S be a nonempty finite subset of a torsion-free group G such that S = A ∪ B, where A and B are disjoint abelian sets. If |S²| ≤ 3k − 3, ⟨S⟩ is abelian." Here k = |S|. DecidableEq is implementation structure, classically available for every type.

**Definition 1.7 (Conjecture 6.2).**

$$(claim62) \Leftrightarrow (\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \Rightarrow ((\operatorname{DecidableEq}\left(G\right)) \Rightarrow ((\operatorname{IsTorsionFreeGroup}\left(G\right)) \Rightarrow (\forall S \in \operatorname{Finset}\left(G\right), A \in \operatorname{Finset}\left(G\right), B \in \operatorname{Finset}\left(G\right), C \in \operatorname{Finset}\left(G\right),\; (\operatorname{Nonempty}\left(S\right)) \Rightarrow ((S = (A \cup B) \cup C) \Rightarrow ((\operatorname{Disjoint}\left(A, B\right)) \Rightarrow ((\operatorname{Disjoint}\left(A, C\right)) \Rightarrow ((\operatorname{Disjoint}\left(B, C\right)) \Rightarrow ((\operatorname{IsAbelianSet}\left((A : \operatorname{Set}\left(G\right))\right)) \Rightarrow ((\operatorname{IsAbelianSet}\left((B : \operatorname{Set}\left(G\right))\right)) \Rightarrow ((\operatorname{IsAbelianSet}\left((C : \operatorname{Set}\left(G\right))\right)) \Rightarrow ((Finset.card\left(S \cdot S\right) \le 3 \cdot Finset.card\left(S\right) - 4) \Rightarrow (\operatorname{IsAbelianSet}\left((S : \operatorname{Set}\left(G\right))\right))))))))))))))$$

*Formalization.* `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim62` (`✓ std3`).

*Citation.* Mohan, Neetu (2026). *On small doubling in right-ordered groups and Baumslag-Solitar groups - II*. DOI: [10.48550/arXiv.2607.11194](https://doi.org/10.48550/arXiv.2607.11194). URL: <https://arxiv.org/abs/2607.11194v1>.

*Commentary.*

The paper states: "Conjecture 6.2. Let S be a nonempty finite subset of a torsion-free group G such that S = A ∪ B ∪ C, where A, B, C are pairwise disjoint abelian sets. If |S²| ≤ 3k − 4, ⟨S⟩ is abelian." Here k = |S|. DecidableEq is implementation structure, classically available for every type.

**Theorem 1.8 (A counterexample containing the identity).**

$$\neg claim63$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63` (`✓ std3`). ∎

*Resolves.* `Problems/mohan-neetu-small-doubling-conjecture-63-refutation` (refuted) by `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mohan-neetu-small-doubling-conjecture-63-refutation","declaration_gid":"D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take S = {(0,0),(0,1),(1,1)}. Its product set is {(-1,2),(0,0),(0,1),(0,2),(1,1),(1,2)}, so |S|=3 and |S²|=6=3|S|-3. The identity belongs to S, while (0,1)(1,1)=(-1,2) and (1,1)(0,1)=(1,2). The coordinate proof that the ambient group is torsion-free is shared by all three results.

**Theorem 1.9 (Two disjoint abelian pieces).**

$$\neg claim61$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61` (`✓ std3`). ∎

*Resolves.* `Problems/mohan-neetu-small-doubling-conjecture-61-refutation` (refuted) by `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mohan-neetu-small-doubling-conjecture-61-refutation","declaration_gid":"D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use the same S, with A={(0,0),(0,1)} and B={(1,1)}. The pieces are disjoint and generate abelian subgroups, while S has the same six products and contains the same noncommuting pair.

**Theorem 1.10 (Three singleton abelian pieces).**

$$\neg claim62$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62` (`✓ std3`). ∎

*Resolves.* `Problems/mohan-neetu-small-doubling-conjecture-62-refutation` (refuted) by `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mohan-neetu-small-doubling-conjecture-62-refutation","declaration_gid":"D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take S={(1,1),(2,1),(3,1)} and let A, B and C be its singleton pieces. The product set is {(-2,2),(-1,2),(0,2),(1,2),(2,2)}, so |S²|=5=3|S|-4. Yet (1,1)(2,1)=(-1,2) and (2,1)(1,1)=(1,2).

## References

- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.IsAbelianSet`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.IsTorsionFreeGroup`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.KleinBottleGroup`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim61`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim62`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.claim63`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.instGroupKleinBottleGroup`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result61`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result62`
- Truth anchor: `D5/S0/Certificates/Groups/MohanNeetuSmallDoublingRefutation.result63`
