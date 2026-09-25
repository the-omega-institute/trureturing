# Part (i) of Ishikawa and Koutschan's Pfaffian conjecture is false as printed

## Abstract

At k = n = 2 the Pfaffian of the matrix of the second column of the Motzkin triangle is -8, while the printed product in part (i) of Ishikawa and Koutschan's Conjecture conj.gen is 8.

**Definition 1.1 (Columns of the Motzkin triangle).**

$$\forall k \in \mathbb{N},\; \forall i \in \mathbb{N},\; \operatorname{motzkinTriangle}\left(k, i\right) = \operatorname{card}\left(\{w \in \left(\operatorname{Fin}\left(i - 1\right) \to \operatorname{Fin}\left(3\right)\right) \mid (\forall t \in \operatorname{Finset.range}\left(i\right),\; 0 \le \operatorname{heightAfter}\left(w, t\right)) \land (\operatorname{heightAfter}\left(w, i - 1\right) = k - 1)\}\right)$$

*Formalization.* `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.motzkinTriangle` (`✓ std3`).

*Citation.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

A step word of length i - 1 over U = (1,1), H = (1,0) and D = (1,-1) is a Motzkin path from (0,0) to (i - 1, k - 1) when its height never falls below zero and ends at k - 1; heightAfter(w,t) is the height after the first t steps and stepRise maps U, H, D to 1, 0, -1. The count is the entry M^(k)_i of the source. At i = 0 it enters the matrix only on the diagonal, where the factor j - i vanishes.

**Definition 1.2 (The Hankel-type skew matrix).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall q \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{pfaffianMatrix}\left(k, n\right)\left(p, q\right) = (q - p) \cdot \operatorname{motzkinTriangle}\left(k, p + q\right)$$

*Formalization.* `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.pfaffianMatrix` (`✓ std3`).

*Citation.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

The entry in row p and column q, indexed from zero, is (q - p) M^(k)_(p+q); with i = p + 1 and j = q + 1 this is the source's entry (j - i) M^(k)_(i+j-2) for 1 <= i, j <= 2n.

**Definition 1.3 (The Pfaffian).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2 \cdot n\right), \operatorname{Fin}\left(2 \cdot n\right), \mathbb{Z}\right),\; \operatorname{pfaffian}\left(A\right) = \sum_{sigma \in \{sigma \in \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2 \cdot n\right)\right) \mid (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{sigma}\left(2 \cdot i\right) < \operatorname{sigma}\left(2 \cdot i + 1\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (i < j) \Rightarrow (\operatorname{sigma}\left(2 \cdot i\right) < \operatorname{sigma}\left(2 \cdot j\right)))\}} \operatorname{sign}\left(sigma\right) \cdot \prod_{i \in \operatorname{Fin}\left(n\right)} A\left(\operatorname{sigma}\left(2 \cdot i\right), \operatorname{sigma}\left(2 \cdot i + 1\right)\right)$$

*Formalization.* `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.pfaffian` (`✓ std3`).

*Citation.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

The source defines Pf(A) as the sum over the partitions of [2n] into two-element subsets of the sign of the listing permutation times the product of the paired entries. The formal sum lists each partition once, by the permutations sigma whose pairs {sigma(2i), sigma(2i+1)} are increasing and ordered by their first elements.

**Definition 1.4 (The printed right-hand side).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{printedValue}\left(k, n\right) = \operatorname{ite}\left(k \mid n, \prod_{i \in \operatorname{Finset.range}\left(\operatorname{NatDiv}\left(n, k\right)\right)} \prod_{j \in \operatorname{Finset.range}\left(k\right)} (4 \cdot k \cdot i + 2 \cdot j + k), \operatorname{ite}\left((\operatorname{NatMod}\left(k, 2\right) = 1) \land (k \mid n + \operatorname{NatDiv}\left(k, 2\right)), \prod_{j \in \operatorname{Finset.Icc}\left(1, \operatorname{NatDiv}\left(k, 2\right)\right)} \frac{1}{2 \cdot j - k} \cdot \prod_{i \in \operatorname{Finset.range}\left(\operatorname{NatDiv}\left(n + \operatorname{NatDiv}\left(k, 2\right), k\right)\right)} \prod_{j \in \operatorname{Finset.Icc}\left(1, k\right)} (4 \cdot k \cdot i + 2 \cdot j - k), 0\right)\right)$$

*Formalization.* `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.printedValue` (`✓ std3`).

*Citation.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

The first branch is the product for m = n/k when k divides n; the second is the product for odd k with m = (n + floor(k/2))/k when k divides n + floor(k/2); all other cases give zero. Natural-number division and remainder are written NatDiv and NatMod.

**Definition 1.5 (Part (i) of Conjecture conj.gen).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; ((0 < k) \land (0 < n)) \Rightarrow (\operatorname{pfaffian}\left(\operatorname{pfaffianMatrix}\left(k, n\right)\right) = \operatorname{printedValue}\left(k, n\right)))$$

*Formalization.* `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.claim` (`✓ std3`).

*Citation.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

For all positive integers k and n the Pfaffian of the matrix equals the printed value. At k = 1 this is the source's Theorem thm.pfMotz. Part (ii) of the conjecture is not part of this statement.

**Theorem 1.6 (A sign counterexample at k = n = 2).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ishikawa-koutschan-2012-motzkin-triangle-pfaffian-refutation` (refuted) by `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ishikawa-koutschan-2012-motzkin-triangle-pfaffian-refutation","declaration_gid":"D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Masao Ishikawa, Christoph Koutschan (2012). *Zeilberger's Holonomic Ansatz for Pfaffians*. DOI: [10.48550/arXiv.1201.5253](https://doi.org/10.48550/arXiv.1201.5253). URL: <https://arxiv.org/abs/1201.5253v2>.

*Commentary.*

The column M^(2)_1, ..., M^(2)_5 is 0, 1, 2, 5, 12, so the upper entries of the 4 x 4 matrix are a12 = 0, a13 = 2, a14 = 6, a23 = 2, a24 = 10, a34 = 12, and its Pfaffian is a12 a34 - a13 a24 + a14 a23 = 0 - 20 + 12 = -8. Since 2 divides 2 with m = 1, the printed value is the product of 4km + 2j + k over m = 0 and j = 0, 1, namely 2 times 4, which is 8. The kernel evaluates both sides.

## References

- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.claim`
- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.motzkinTriangle`
- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.pfaffian`
- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.pfaffianMatrix`
- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.printedValue`
- Truth anchor: `D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result`
