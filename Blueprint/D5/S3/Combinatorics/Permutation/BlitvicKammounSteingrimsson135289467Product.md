# BlitvicKammounSteingrimsson135289467Product

## Abstract

Symbolic order relations and cardinalities for the 135289467 packing count.

**Definition 1.1 (claim).**

$$claim \iff (count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 1 = 1 \land count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 2 = 30 \land (\forall (j : \mathbb{N}) , 3 \le j \to count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 j = (121 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 0 + 168 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 1 + 72 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 2) \cdot count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 (j - 1)))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.claim` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The enumeration for 135289467 with overlap 3, for example, has a product formula according to our data, but the successive factors are not single binomial coefficients. However, the factors are polynomial starting from $j = 3$, namely $121\begin{pmatrix}j-3\\0\end{pmatrix}+168\begin{pmatrix}j-3\\1\end{pmatrix}+72\begin{pmatrix}j-3\\2\end{pmatrix}$, in the binomial basis.

Section 7 item 10, page 49. The vector decreases positions and ranks by one. The count is the original cardinality of permutations of length 9+6(j-1), with additional occurrences allowed. The two initial values refer to that same cardinality; the recurrence quantifies every natural j with 3≤j.

**Theorem 1.2 (result).**

$$count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 1 = 1 \land count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 2 = 30 \land (\forall (j : \mathbb{N}) , 3 \le j \to count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 j = (121 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 0 + 168 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 1 + 72 \cdot \operatorname{Nat} . \operatorname{choose} (j - 3) 2) \cdot count (! [ 0 , 2 , 4 , 1 , 7 , 8 , 3 , 5 , 6 ] : Fin 9 \to Fin 9) 3 (j - 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.result` (`✓ std3`). ∎

*Resolves.* `Problems/bks10-product` (proved) by `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bks10-product","declaration_gid":"D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The two initial counts and the recurrence hold for all the displayed indices. Deleting six labels leaves the previous residual order shifted by six; two disjoint shuffles give the square multiplier.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.result`
- Dependency: [D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core](BlitvicKammounSteingrimsson135289467Core.md)
- Dependency: [D5/S3/Combinatorics/Permutation/PackingMaximumRefutation](PackingMaximumRefutation.md)
