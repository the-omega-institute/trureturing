# Nathanson's Additive h-Basis Strict-Inequality Refutation

## Abstract

The strict inequality in Nathanson's Problem 12(2) fails for a three-element integer set.

Here h • A denotes the h-fold sumset A + ... + A, with repetitions allowed. val denotes the coercion from natural numbers to integers. The expression sSup is the natural-number supremum. On the source domain used by the claim, the relevant sets are nonempty and bounded, so this supremum is a maximum.

Problem 12. It is natural to ask how the use of negative numbers changes the size of the maximal interval [0, n] contained in an h-fold sumset. For integers h ≥ 2 and k ≥ 2, are the following statements true or false? (1) If A ∈ (ℤ choose k) with min(A) < 0, then ℓ_h(A) ≤ n♭_h(k). (2) If A ∈ (ℤ choose k) with min(A) < 0, then ℓ_h(A) < n♭_h(k). Only statement (2) is settled here.

**Definition 1.1 (Largest covered initial segment).**

$$\forall h \in \mathbb{N},\; \forall A \in \operatorname{Finset}\left(\mathbb{Z}\right),\; \operatorname{segmentLength}\left(h, A\right) = \operatorname{sSup}\left(\{n \in \mathbb{N} \mid \forall i \in \mathbb{N},\; (i \le n) \Rightarrow (\operatorname{val}\left(i\right) \in \operatorname{nsmul}\left(h, A\right))\}\right)$$

*Formalization.* `D5/S3/Arith/NathansonAdditiveHBasisRefutation.segmentLength` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

For h in N and a finite integer set A, segmentLength(h,A) is the largest natural n for which every natural i <= n, coerced to an integer, belongs to h • A.

**Definition 1.2 (Maximum over nonnegative k-sets).**

$$\forall h \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{nonnegativeMaximum}\left(h, k\right) = \operatorname{sSup}\left(\{n \in \mathbb{N} \mid \exists B \in \operatorname{Finset}\left(\mathbb{N}\right),\; (\operatorname{card}\left(B\right) = k) \land (\forall i \in \mathbb{N},\; (i \le n) \Rightarrow (i \in \operatorname{nsmul}\left(h, B\right)))\}\right)$$

*Formalization.* `D5/S3/Arith/NathansonAdditiveHBasisRefutation.nonnegativeMaximum` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

For h,k in N, nonnegativeMaximum(h,k) is the largest covered endpoint among all k-element finite subsets B of N. This is n♭_h(k).

**Definition 1.3 (The strict universal claim).**

$$(claim) \Leftrightarrow (\forall h \in \mathbb{N},\; \forall k \in \mathbb{N},\; (2 \le h) \Rightarrow \left((2 \le k) \Rightarrow (\forall A \in \operatorname{Finset}\left(\mathbb{Z}\right),\; (\operatorname{card}\left(A\right) = k) \Rightarrow \left((\exists a \in \mathbb{Z},\; (a \in A) \land (a < 0)) \Rightarrow \left((0 \in \operatorname{nsmul}\left(h, A\right)) \Rightarrow (\operatorname{segmentLength}\left(h, A\right) < \operatorname{nonnegativeMaximum}\left(h, k\right))\right)\right))\right))$$

*Formalization.* `D5/S3/Arith/NathansonAdditiveHBasisRefutation.claim` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

The claim quantifies h >= 2, k >= 2, and every k-element finite integer set A that contains a negative element and satisfies 0 in h • A. The last premise excludes exactly the cases in which the source leaves ℓ_h(A) undefined.

**Theorem 1.4 (Equality at a negative three-set).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/NathansonAdditiveHBasisRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-additive-h-bases-problem-12` (refuted) by `D5/S3/Arith/NathansonAdditiveHBasisRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-additive-h-bases-problem-12","declaration_gid":"D5/S3/Arith/NathansonAdditiveHBasisRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

Take h=2, k=3, and A={-1,1,2}. Then 2A={-2,0,1,2,3,4}, so ℓ_2(A)=4. The set {0,1,2} shows n♭_2(3)>=4. Conversely, a three-element B subset N whose double sumset covers 0 through 5 must contain 0 and 1. Representing 3 forces its third element to be 2 or 3, but neither {0,1,2} nor {0,1,3} represents 5. Hence n♭_2(3)=4, contradicting the proposed strict inequality.

## References

- Truth anchor: `D5/S3/Arith/NathansonAdditiveHBasisRefutation.claim`
- Truth anchor: `D5/S3/Arith/NathansonAdditiveHBasisRefutation.nonnegativeMaximum`
- Truth anchor: `D5/S3/Arith/NathansonAdditiveHBasisRefutation.result`
- Truth anchor: `D5/S3/Arith/NathansonAdditiveHBasisRefutation.segmentLength`
