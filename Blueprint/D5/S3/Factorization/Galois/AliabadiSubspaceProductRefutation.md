# A degree-seven counterexample to the subspace-product conjecture

## Abstract

The degree-seven field Q[X]/(X^7-2) refutes Aliabadi's subspace-product lower bound: there are no proper nontrivial intermediate fields, but two five-dimensional subspaces have product span of dimension at most seven, below the proposed lower bound nine.

**Definition 1.1 (Multiplicative field translates).**

$$\forall (K:Type), \forall (L:Type), [\operatorname{Field}\left(K\right)], [\operatorname{Field}\left(L\right)], [\operatorname{Algebra}\left(K, L\right)], \forall (a:L), \forall (M:\operatorname{IntermediateField}\left(K, L\right)), \operatorname{translate}\left(a, M\right) = \operatorname{map}\left(\operatorname{mulLeft}\left(K, a\right), M\right)$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.translate` (`✓ std3`).

*Citation.* Mohsen Aliabadi (2025). *Conditions for matchability in groups and field extensions II*. DOI: [10.7151/dmgaa.1461](https://doi.org/10.7151/dmgaa.1461). URL: <https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461>.

*Commentary.*

K and L are arbitrary fields equipped with a K-algebra structure on L. M is an actual intermediate field. Its underlying K-subspace is mapped by the K-linear map x mapped to a times x. Thus translate(a,M) consists exactly of the products am for m in M. The scalar a may be zero.

**Definition 1.2 (The full intermediate-field premise).**

$$\forall (K:Type), \forall (L:Type), [\operatorname{Field}\left(K\right)], [\operatorname{Field}\left(L\right)], [\operatorname{Algebra}\left(K, L\right)], \forall (A:\operatorname{Submodule}\left(K, L\right)), \forall (B:\operatorname{Submodule}\left(K, L\right)), \operatorname{intersectionPremise}\left(A, B\right) \Leftrightarrow \forall (a:L), \forall (b:L), \forall (M:\operatorname{IntermediateField}\left(K, L\right)), \left(\operatorname{bot}\left(\right) < M \land \left(M < \operatorname{top}\left(\right) \land \operatorname{FiniteDimensional}\left(K, M\right)\right)\right) \Rightarrow \operatorname{finrank}\left(K, \operatorname{inf}\left(\operatorname{translate}\left(a, M\right), A\right)\right)+\operatorname{finrank}\left(K, \operatorname{inf}\left(\operatorname{translate}\left(b, M\right), B\right)\right) \le \operatorname{finrank}\left(K, M\right)+1$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.intersectionPremise` (`✓ std3`).

*Citation.* Mohsen Aliabadi (2025). *Conditions for matchability in groups and field extensions II*. DOI: [10.7151/dmgaa.1461](https://doi.org/10.7151/dmgaa.1461). URL: <https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461>.

*Commentary.*

The predicate quantifies over every a and b in L and every finite-dimensional intermediate field M that properly contains K and is properly contained in L. Bottom represents the embedded base field and top represents L. Intersections are submodule infima; finrank is dimension over K, and finrank(K,M) is the degree [M:K]. The full ambient field is excluded from this premise.

**Definition 1.3 (The whole original conjecture).**

$$claim \Leftrightarrow \forall (K:Type), \forall (L:Type), [\operatorname{Field}\left(K\right)], [\operatorname{Field}\left(L\right)], [\operatorname{Algebra}\left(K, L\right)], \forall (A:\operatorname{Submodule}\left(K, L\right)), \forall (B:\operatorname{Submodule}\left(K, L\right)), \left(\operatorname{FiniteDimensional}\left(K, A\right) \land \left(\operatorname{FiniteDimensional}\left(K, B\right) \land \left(0 < \operatorname{finrank}\left(K, A\right) \land \left(0 < \operatorname{finrank}\left(K, B\right) \land \operatorname{intersectionPremise}\left(A, B\right)\right)\right)\right)\right) \Rightarrow \forall (S:\operatorname{Submodule}\left(K, L\right)), \forall (T:\operatorname{Submodule}\left(K, L\right)), \left(S \le A \land T \le B\right) \Rightarrow \operatorname{finrank}\left(K, S\right)+\operatorname{finrank}\left(K, T\right)-1 \le \operatorname{finrank}\left(K, \operatorname{span}\left(K, S T\right)\right)$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.claim` (`✓ std3`).

*Citation.* Mohsen Aliabadi (2025). *Conditions for matchability in groups and field extensions II*. DOI: [10.7151/dmgaa.1461](https://doi.org/10.7151/dmgaa.1461). URL: <https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461>.

*Commentary.*

This is Conjecture 5.1 of arXiv:2309.14664v1-v3, section 5.1, and Conjecture 38 of the journal article, printed page 154. K and L range over fields with a K-algebra structure on L. A and B are arbitrary finite-dimensional K-subspaces of positive dimensions. S and T range over all K-subspaces of L contained in A and B respectively. No equality of dimensions, separability, infinite-extension condition, dimension-sum restriction, or cap by [L:K] is imposed. The notation span(K,ST) denotes the K-linear span of the actual pointwise product set {st : s in S, t in T}, as defined in section 2.2. The subtraction is natural-number subtraction; at zero-dimensional S and T this gives the same inequality as the ordinary integer interpretation.

**Definition 1.4 (The defining polynomial).**

$$polynomial = X^{7}-2$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial has rational coefficients. Its integer counterpart is monic and Eisenstein at the prime ideal generated by two: all lower coefficients are divisible by two and the constant coefficient is not divisible by four. Gauss's lemma transfers irreducibility to Q[X].

**Definition 1.5 (The realized quotient field).**

$$Extension = \operatorname{AdjoinRoot}\left(polynomial\right)$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.Extension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AdjoinRoot is the actual quotient Q[X]/(X^7-2). Irreducibility supplies its field structure. Its canonical power basis has dimension seven, hence it is finite-dimensional over Q. The base-field map is the injective algebra map into this nontrivial field.

**Definition 1.6 (The class of X).**

$$alpha = \operatorname{root}\left(polynomial\right)$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alpha is the quotient class of X. The quotient-root identity gives alpha to the seventh power equal to two. The canonical basis is 1, alpha, alpha squared, through alpha to the sixth.

**Definition 1.7 (Nonconstant power spans).**

$$\forall (n:\mathbb{N}), \operatorname{powerSpan}\left(n\right) = \operatorname{span}\left(\mathbb{Q}, \operatorname{range}\left(\lambda (i:\operatorname{Fin}\left(n\right))\mapsto alpha^{\operatorname{val}\left(i\right)+1}\right)\right)$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.powerSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural number n, powerSpan(n) is the span of the actual powers alpha through alpha to the n. Fin n indexes exponents i+1. For n at most six these are distinct entries of the quotient's power basis, so their span has dimension n and does not contain the constant basis vector 1. In particular powerSpan(5) is properly contained in powerSpan(6), and powerSpan(6) is proper in Extension.

**Definition 1.8 (The realized countermodel certificate).**

$$countermodel \Leftrightarrow \begin{aligned}\operatorname{finrank}\left(\mathbb{Q}, Extension\right) = 7, alpha^{7} = 2,\\\operatorname{finrank}\left(\mathbb{Q}, \operatorname{powerSpan}\left(6\right)\right) = 6, \operatorname{finrank}\left(\mathbb{Q}, \operatorname{powerSpan}\left(5\right)\right) = 5,\\\operatorname{powerSpan}\left(5\right) < \operatorname{powerSpan}\left(6\right), \operatorname{powerSpan}\left(6\right) < \operatorname{top}\left(\right),\\\neg 1 \in \operatorname{powerSpan}\left(6\right), \neg 1 \in \operatorname{powerSpan}\left(5\right),\\\operatorname{intersectionPremise}\left(\operatorname{powerSpan}\left(6\right), \operatorname{powerSpan}\left(6\right)\right),\\\operatorname{finrank}\left(\mathbb{Q}, \operatorname{span}\left(\mathbb{Q}, \operatorname{powerSpan}\left(5\right) \operatorname{powerSpan}\left(5\right)\right)\right) \le 7\end{aligned}$$

*Formalization.* `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.countermodel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take A=B=powerSpan(6) and S=T=powerSpan(5). These have dimensions six and five, S is properly contained in A, A is proper in L, and 1 is absent from both. Prime extension degree seven makes every intermediate field bottom or top, so the full premise holds for every scalar pair. The actual span of products of S and T is a submodule of the seven-dimensional field; its dimension is therefore at most seven. This upper bound is sufficient, and no equality of that span with the field is asserted here.

**Theorem 1.9 (The uncapped universal bound is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mohsen Aliabadi (2025). *Conditions for matchability in groups and field extensions II*. DOI: [10.7151/dmgaa.1461](https://doi.org/10.7151/dmgaa.1461). URL: <https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461>.

*Commentary.*

Applying the conjectured conclusion to the realized field and the selected subspaces would give a product-span dimension at least 5+5-1=9. The ambient field bounds that same dimension above by seven, a contradiction. The premise excludes the full intermediate field L and has no other intermediate field to test in prime degree. The refutation therefore concerns the whole original conjecture, including its full intermediate-field premise. It also uses strict proper subspaces, so replacing the ordinary containment symbols by strict containment does not remove this counterexample.

## References

- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.Extension`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.alpha`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.claim`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.countermodel`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.intersectionPremise`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.polynomial`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.powerSpan`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.result`
- Truth anchor: `D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.translate`
