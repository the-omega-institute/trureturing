# Result

## Abstract

Every greedy output on the star family has an additive gap r.

**Definition 1.1 (claim).**

$$\operatorname{claim} \iff (\forall \operatorname{r} : \mathbb{N} , 1 \leq \operatorname{r} \to \exists \operatorname{n} : \mathbb{N} , \exists \operatorname{G} : \operatorname{SimpleGraph} (\operatorname{Fin} \operatorname{n}) , \exists \gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{Fin} 4 , \operatorname{G} . \operatorname{Connected} \land \operatorname{Function} . \operatorname{Surjective} \gamma \land \operatorname{wildNumber} \operatorname{G} \gamma = 5 * \operatorname{r} \land (\exists \operatorname{W} , \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W}) \land (\forall \operatorname{W} , \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W} \to \operatorname{W} . \operatorname{card} = 6 * \operatorname{r}))$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.claim` (`✓ std3`).

*Citation.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Section 7, PDF page 21: “How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .” The graph is finite, connected, and colored surjectively with Fin 4. Every possible output has 6r edges and the minimum color-connecting size is 5r.

**Theorem 1.2 (result).**

$$\forall \operatorname{r} : \mathbb{N} , 1 \leq \operatorname{r} \to \exists \operatorname{n} : \mathbb{N} , \exists \operatorname{G} : \operatorname{SimpleGraph} (\operatorname{Fin} \operatorname{n}) , \exists \gamma : \operatorname{G} . \operatorname{edgeSet} \to \operatorname{Fin} 4 , \operatorname{G} . \operatorname{Connected} \land \operatorname{Function} . \operatorname{Surjective} \gamma \land \operatorname{wildNumber} \operatorname{G} \gamma = 5 * \operatorname{r} \land (\exists \operatorname{W} , \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W}) \land (\forall \operatorname{W} , \operatorname{IsGreedyOutput} \operatorname{G} \gamma \operatorname{W} \to \operatorname{W} . \operatorname{card} = 6 * \operatorname{r})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap` (proved) by `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap","declaration_gid":"D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik (2025). *The Wild Number of an Edge-Colored Graph*. DOI: [10.48550/arXiv.2508.06711](https://doi.org/10.48550/arXiv.2508.06711). URL: <https://arxiv.org/abs/2508.06711v1>.

*Commentary.*

Section 7, PDF page 21: “How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .” The graph is finite, connected, and colored surjectively with Fin 4. Every possible output has 6r edges and the minimum color-connecting size is 5r.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.claim`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result.result`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph](AmalgamGraph.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamWild](AmalgamWild.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy](Greedy.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/Relabel](Relabel.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate](WheelCertificate.md)
