# Restricted Generalized Schur Numbers

## Abstract

Restricted generalized Schur numbers and the eventual equality in Open Question 6.2 of Gaiser.

**Definition 1.1 (Monochromatic solutions with a prescribed number of distinct values).**

$$HasMonochromaticSolution\left(r, k, l, n, c\right) \Leftrightarrow \left(\exists x \in Fin\left(k + 1\right) \to Nat,\; \left(\forall i \in Fin\left(k + 1\right),\; 1 \le x\left(i\right) \land x\left(i\right) \le n\right) \land \left(\sum _{i \in Fin\left(k\right)} x\left(castSucc\left(i\right)\right) = x\left(last\left(k\right)\right) \land \left(card\left(image\left(x, univ\left(Fin\left(k + 1\right)\right)\right)\right) = l + 1 \land \left(\forall i \in Fin\left(k + 1\right),\; \forall j \in Fin\left(k + 1\right),\; c\left(x\left(i\right)\right) = c\left(x\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.HasMonochromaticSolution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

A colouring c maps the natural numbers to Fin(r); only its values from 1 through n matter. The tuple x has k summands and a final value equal to their sum. Every entry lies between 1 and n, the image of the tuple has exactly l+1 elements, and all entries have the same colour. Repeated summands are permitted.

**Definition 1.2 (The restricted generalized Schur number).**

$$schur\left(r, k, l\right) = sInf\left(\{ n: Nat \mid \forall c \in Nat \to Fin\left(r\right),\; HasMonochromaticSolution\left(r, k, l, n, c\right) \} \right)$$

*Formalization.* `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.schur` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

The number S_r(k;l) is the infimum in the natural numbers of the set of n for which every r-colouring has such a solution. If this set is nonempty, the infimum is its least element; the infimum of the empty set is zero. Gaiser's definition concerns k at least 2.

**Definition 1.3 (The equality proposed in Open Question 6.2).**

$$claim \Leftrightarrow \left(\exists K \in Nat,\; \forall k \in Nat,\; K \le k \Rightarrow schur\left(3, k, 2\right) = k^{3} + 3 \cdot k^{2} + k - 1\right)$$

*Formalization.* `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Collier Gaiser (2026). *Restricted generalized Schur numbers*. DOI: [10.48550/arXiv.2608.08789](https://doi.org/10.48550/arXiv.2608.08789). URL: <https://arxiv.org/abs/2608.08789v1>.

*Commentary.*

The proposed equality asserts the existence of a natural threshold K such that S_3(k;2) equals k^3+3k^2+k-1 for every natural k at least K. The subtraction in this expression is natural-number subtraction.

## References

- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.HasMonochromaticSolution`
- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs.schur`
