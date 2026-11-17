# CycleDeficit

## Abstract

A finite binomial sum gives every Italian domination coefficient of a labelled simple cycle.

**Definition 1.1 (binom).**

$$\forall (u v : \mathbb{Z}) , \operatorname{binom} u v = \operatorname{if} 0 \leq u \land 0 \leq v \operatorname{then} (\operatorname{Nat}.\operatorname{choose} u . \operatorname{toNat} v . \operatorname{toNat} : \mathbb{Q}) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.binom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Ordinary binomial coefficients are extended by zero when either integer index is negative. For a nonnegative top an oversized bottom also has value zero.

**Definition 1.2 (zero Free).**

$$\forall (n j : \mathbb{N}) , \operatorname{zeroFree} n j = \operatorname{let} r : \mathbb{Z} := (j : \mathbb{Z}) - (n : \mathbb{Z}) ; \operatorname{let} s : \mathbb{Z} := 2 * (n : \mathbb{Z}) - (j : \mathbb{Z}) ; \operatorname{if} 0 \leq r \land 2 * r \leq (n : \mathbb{Z}) \land 0 < s \operatorname{then} (n : \mathbb{Q}) / (s : \mathbb{Q}) * \operatorname{binom} s r \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.zeroFree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

This term counts valid deficit words without a zero. The integer tests make the divisor positive before the rational division.

**Definition 1.3 (all Exceptional).**

$$\forall (n j : \mathbb{N}) , \operatorname{allExceptional} n j = \operatorname{if} \operatorname{Nat}.\operatorname{mod} n 3 = 0 \land 3 * j = 4 * n \operatorname{then} 3 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.allExceptional` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

This term records the three labelled shifts of a repetition of [0,2,2]. Nat.mod is natural-number remainder.

**Definition 1.4 (gap Term).**

$$\forall (n j a b : \mathbb{N}) , \operatorname{gapTerm} n j a b = \operatorname{let} c : \mathbb{Z} := (j : \mathbb{Z}) - 2 * (a : \mathbb{Z}) - 4 * (b : \mathbb{Z}) ; \operatorname{let} t : \mathbb{Z} := (n : \mathbb{Z}) - (j : \mathbb{Z}) + (a : \mathbb{Z}) + (b : \mathbb{Z}) ; \operatorname{let} m : \mathbb{Z} := t + (b : \mathbb{Z}) ; \operatorname{if} 0 \leq c \land 1 \leq t \operatorname{then} (n : \mathbb{Q}) / (m : \mathbb{Q}) * \operatorname{binom} m (b : \mathbb{Z}) * \operatorname{binom} (c + t - 1) c * \operatorname{binom} (c + t) (a : \mathbb{Z}) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.gapTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The integer parameters c, t and m give the number of ones, ordinary gaps and zeros. The tests require nonnegative c and positive t. Every displayed slash is rational division; its denominator is positive in the included case.

**Definition 1.5 (closed Form).**

$$\forall (n j : \mathbb{N}) , \operatorname{closedForm} n j = \operatorname{zeroFree} n j + \operatorname{allExceptional} n j + \sum_{b \in \operatorname{Finset}.\operatorname{range} (j + 1)} \sum_{a \in \operatorname{Finset}.\operatorname{range} (j + 1)} \operatorname{gapTerm} n j a b$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.closedForm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The two sums range over 0 through j. Outside the permissible gap parameters the summand is zero, so these finite ranges contain every contribution.

**Definition 1.6 (claim).**

$$\operatorname{claim} = \forall (n : \mathbb{N}) (j : \mathbb{N}) , 3 \leq n \to j \leq 2 * n \to (\operatorname{dI} n (2 * n - j) : \mathbb{Q}) = \operatorname{closedForm} n j$$

*Formalization.* `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

The assertion gives the finite coefficient sum for every n ≥ 3 and 0 ≤ j ≤ 2n, answering the fourth question of Shao and Zhao, §9 (p. 29). The carrier Fin n fixes the vertex labels; no rotation or reflection quotient is taken. The value at weight zero is the same subtype count.

**Theorem 1.7 (result).**

$$\forall (n : \mathbb{N}) (j : \mathbb{N}) , 3 \leq n \to j \leq 2 * n \to (\operatorname{dI} n (2 * n - j) : \mathbb{Q}) = \operatorname{closedForm} n j$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result` (`✓ std3`). ∎

*Resolves.* `Problems/shao-zhao-italian-cycle-closed-form` (proved) by `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shao-zhao-italian-cycle-closed-form","declaration_gid":"D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Complement each label f(i) to 2−f(i). A pair of consecutive twos must be flanked by zeros; every zero-free gap is either exactly [2,2] or has no adjacent twos. Marking a zero gives ordered gaps, and removing the mark multiplies the count by the number of zeros, even for periodic words. Weak compositions distribute the ones; subsets of insertion slots place the isolated twos. The all-exceptional case contributes three labelled shifts. Marking a one counts the class without zeros. The disjoint classes yield the displayed identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.allExceptional`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.binom`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.closedForm`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.gapTerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.zeroFree`
- Dependency: [D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords](OrdinaryWords.md)
- Dependency: [D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps](RootedCycleGaps.md)
