# Quantitative word orthonormal extension

## Abstract

A common orthonormal extension has small contraction residuals and bounded short-word coefficients.

**Theorem 1.1 (A threshold-stable extension with word certificates).**

$$\forall D : \mathbb{N}, \forall r : \mathbb{N}, \forall M : \mathbb{N}, \forall delta : \mathbb{R}, \forall A : \operatorname{Fin}\left(M\right) \to \operatorname{End}_{\mathbb{C}}(\mathbb{C}^{D}), \forall eta : \operatorname{Fin}\left(r\right) \to \mathbb{C}^{D}, ((2 \le r) \land ((r \le D) \land ((M \le D^{2}) \land ((0<delta) \land ((delta<1) \land ((\forall a : \operatorname{Fin}\left(M\right), \forall x : \mathbb{C}^{D}, \left\lVert A\left(a\right)\left(x\right) \right\rVert \le \left\lVert x \right\rVert) \land (\operatorname{Orthonormal}_{\mathbb{C}}\left(eta\right)))))))) \Rightarrow (\exists m : \mathbb{N}, (r \le m) \land ((m \le D) \land (\exists e : \operatorname{Fin}\left(m\right) \to \mathbb{C}^{D}, (\operatorname{Orthonormal}_{\mathbb{C}}\left(e\right)) \land ((\forall b : \operatorname{Fin}\left(r\right), e\left(b\right) = eta\left(b\right)) \land ((\forall a : \operatorname{Fin}\left(M\right), \forall j : \operatorname{Fin}\left(m\right), \left\lVert A\left(a\right)\left(e\left(j\right)\right)-P\left(A\left(a\right)\left(e\left(j\right)\right)\right) \right\rVert \le delta) \land (\exists c : \operatorname{Fin}\left(m\right) \to ((\operatorname{List}\left(\operatorname{Fin}\left(M\right)\right) \times \operatorname{Fin}\left(r\right)) \to_{0} \mathbb{C}), (\forall j : \operatorname{Fin}\left(m\right), \forall w : \operatorname{List}\left(\operatorname{Fin}\left(M\right)\right), \forall b : \operatorname{Fin}\left(r\right), (c\left(j\right)\left(w, b\right) \neq 0) \Rightarrow (\left|w\right| \le m-r)) \land ((\forall j : \operatorname{Fin}\left(m\right), e\left(j\right) = \sum_{(w,b) \in \operatorname{supp}\left(c\left(j\right)\right)} c\left(j\right)\left(w, b\right) A_{w} eta\left(b\right)) \land (\forall j : \operatorname{Fin}\left(m\right), \sum_{(w,b) \in \operatorname{supp}\left(c\left(j\right)\right)} \left|c\left(j\right)\left(w, b\right)\right| \le (\frac{D}{delta})^{m-r}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension.quantitative_word_orthonormal_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D, r and M be natural numbers with 2 <= r <= D and M <= D squared. Let 0 < delta < 1. On the complex Euclidean space of dimension D, let A be an arbitrary family of M linear contractions and let eta be an arbitrary orthonormal family of r seed vectors. There is an integer r <= m <= D and one orthonormal family e of length m whose first r vectors are eta. In the display, Fin(k) means the indices 0 through k-1, End over C means complex-linear endomorphisms, and the arrow with subscript zero denotes finitely supported functions. Put W = span(e) and let P be its orthogonal projection; P depends on the same e quantified in the display. Seed indices in e are included by the order-preserving inclusion Fin(r) into Fin(m). Every residual A(a)e(j) - P(A(a)e(j)) has norm at most delta, simultaneously for every a and j.

For this same e, every vector e(j) has a finitely supported complex coefficient family c(j) on pairs (w,b), with w a list of contraction labels and b a seed index. In the display, supp(c(j)) is the finite set of pairs (w,b) with nonzero coefficient, each sum runs over this support, and the absolute-value bars on w denote its length. It satisfies e(j) = sum c(j)(w,b) A(w)eta(b); every supported word has length at most m-r; and sum of the absolute coefficients is at most (D/delta) to the power m-r. The displayed A with word subscript denotes the chronological word operator: the empty word acts as identity, and appending a label a applies A(a) after the existing word. The Lean expression uses the product of the reversed list of endomorphisms.

To extend a current orthonormal family, take a residual whose norm beta exceeds delta and adjoin its normalization. Orthogonality preserves all preceding vectors. The new vector is beta inverse times A(a)e(j) minus its m orthogonal projection terms. Each projection coefficient has modulus at most one. Transporting the existing finite word certificates therefore increases their word lengths by at most one and multiplies their absolute coefficient bound by at most (m+1)/delta <= D/delta. Dimension limits the number of extensions. At termination every residual meets the threshold.

The empty contraction family, full initial dimension r=D, repeated or zero contractions and arbitrarily small positive thresholds are included. No singular-value, conditioning or previously successful extension premise is imposed. This conclusion concerns the finite-dimensional contraction geometry and its coefficients.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension.quantitative_word_orthonormal_extension`
