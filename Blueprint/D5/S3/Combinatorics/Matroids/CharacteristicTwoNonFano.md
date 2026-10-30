# Characteristic-two opposite intersections

## Abstract

For four arbitrary finite-dimensional subspaces over a field of characteristic two, the sum of the three opposite pair intersections has dimension at most twice the relation deficiency. This is the unrestricted geometric step used by the seven-subspace non-Fano rank-cone certificate.

**Theorem 1.1 (`finrank_opposite_sum_le_two_deficiency`).**

Let `F` be a field of characteristic two, let `V` be a finite-dimensional `F`-module, and let `A B C Z` be submodules of `V`. Then

$$
\begin{aligned}
\operatorname{finrank}\big(&((A+B)\cap(C+Z)) + ((A+C)\cap(B+Z))\\
&+ ((A+Z)\cap(B+C))\big)\\
&\le 2\big(\operatorname{finrank}A+\operatorname{finrank}B+\operatorname{finrank}C+\operatorname{finrank}Z\\
&\qquad-\operatorname{finrank}(A+B+C+Z)\big).
\end{aligned}
$$

*Proof.* The third opposite intersection is contained in the sum of the first two. If `y = a + z = b + c`, characteristic two gives `a+b = c+z`, `a+c = b+z`, and `y = (a+b)+(a+c)`. The Grassmann formula bounds each opposite intersection by the total relation deficiency, and the submodule sum bound finishes the estimate. The proof permits zero, overlapping, and unequal subspaces.

*Lean status.* The declaration is retained as WIP while the canonical targeted kernel build is unavailable; no formal verification claim is made until that build and its scoped report succeed.

*Attribution and boundary.* The theorem is the unrestricted relation-space form needed here. The projection-cancellation mechanism and codimension robustification have an earlier restricted source in Anna Blasiak, Robert Kleinberg, and Eyal Lubetzky, *Lexicographic products and the power of non-linear network coding*, arXiv:1108.2489v1, Lemma 6.2 Eq. (6.1) and Lemma 6.3/Theorem 6.4 Eq. (6.8). This declaration does not claim priority for the characteristic-two inequality, and it does not formalize the remaining seven-subspace `Phi` elimination or the six-party stabilizer bridge.

## References

- `D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano.finrank_opposite_sum_le_two_deficiency`
- Anna Blasiak, Robert Kleinberg, and Eyal Lubetzky, *Lexicographic products and the power of non-linear network coding*, [arXiv:1108.2489v1](https://arxiv.org/abs/1108.2489), Lemma 6.2 Eq. (6.1), Lemma 6.3, and Theorem 6.4 Eq. (6.8).
