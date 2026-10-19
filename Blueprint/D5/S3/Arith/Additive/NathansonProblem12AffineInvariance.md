# Affine invariance of sum intersection sets

## Abstract

Injective affine maps preserve the sum intersection set, answering Nathanson's Problem 12 affirmatively.

**Definition 1.1 (Asymptotically strict decrease).**

$$\forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \operatorname{AsymptoticallyStrictlyDecreasing}\left(A\right) = ((\forall (q : \mathbb{N}^{+}), A\left(q + 1\right) \subseteq A\left(q\right)) \land (\operatorname{Set}.\operatorname{Infinite}\left(\{q : \mathbb{N}^{+} \mid A\left(q\right) \ne A\left(q + 1\right)\}\right)))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.AsymptoticallyStrictlyDecreasing` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Section 2 (p. 3) states: “A sequence (A_q) of subsets of a set S is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ … A decreasing sequence (A_q) is asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q ∈ ℕ.” The positive-natural index type ℕ+ represents the source's ℕ = {1, 2, 3, …}. The set of indices where adjacent sets differ must be infinite.

**Definition 1.2 (The sum intersection set).**

$$\forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \operatorname{H}\left(A\right) = \{h : \mathbb{N} \mid (0 < h) \land (\operatorname{SMul}.\operatorname{smul}\left(h, \operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}^{+}) \mapsto A\left(q\right)\right)\right) = \operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}^{+}) \mapsto \operatorname{SMul}.\operatorname{smul}\left(h, A\left(q\right)\right)\right))\}$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.H` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Section 1 (p. 1) defines “the h-fold sumset hA = {a₁ + a₂ + ⋯ + a_h : a_i ∈ A for all i = 1, …, h}”. It then states (p. 2): “For an additive semigroup S and index set Q, we define the sum intersection set” H(A_q) = {h ∈ ℕ : hA = ⋂_{q∈Q} hA_q}, with A = ⋂_{q∈Q} A_q. Here h is a Lean natural number restricted by 0 < h. SMul.smul h B denotes Mathlib's pointwise h-fold sumset, rather than the image of B under multiplication by h. Set.iInter takes the intersection over every positive-natural index.

**Definition 1.3 (The affirmative answer).**

$$\operatorname{claim} = (\forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \forall (A' : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \forall (s : \mathbb{Z}), \forall (t : \mathbb{Z}), (\operatorname{AsymptoticallyStrictlyDecreasing}\left(A\right)) \Rightarrow ((\operatorname{AsymptoticallyStrictlyDecreasing}\left(A'\right)) \Rightarrow ((\forall (q : \mathbb{N}^{+}), A'\left(q\right) = \operatorname{Set}.\operatorname{image}\left(\operatorname{fun} (a : \mathbb{Z}) \mapsto s \cdot a + t, A\left(q\right)\right)) \Rightarrow ((\neg (s \in (\{0, 1, -1\} : \operatorname{Set}\left(\mathbb{Z}\right)))) \Rightarrow (\operatorname{H}\left(A\right) = \operatorname{H}\left(A'\right))))))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Problem 12 (p. 21) asks verbatim: “Let (A_q) and (A′_q) be asymptotically strictly decreasing sequences of sets of integers such that A′_q = sA_q + t for all q ∈ ℕ and some s, t ∈ ℤ with s ∉ {0, ±1}. Does this imply H(A_q) = H(A′_q)?” The proposition answers this question affirmatively. Integer multiplication followed by translation is expressed by Set.image; both sequences retain the stated decrease assumptions.

**Theorem 1.4 (Affine invariance).**

$$\forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \forall (A' : \mathbb{N}^{+} \to \operatorname{Set}\left(\mathbb{Z}\right)), \forall (s : \mathbb{Z}), \forall (t : \mathbb{Z}), (\operatorname{AsymptoticallyStrictlyDecreasing}\left(A\right)) \Rightarrow ((\operatorname{AsymptoticallyStrictlyDecreasing}\left(A'\right)) \Rightarrow ((\forall (q : \mathbb{N}^{+}), A'\left(q\right) = \operatorname{Set}.\operatorname{image}\left(\operatorname{fun} (a : \mathbb{Z}) \mapsto s \cdot a + t, A\left(q\right)\right)) \Rightarrow ((\neg (s \in (\{0, 1, -1\} : \operatorname{Set}\left(\mathbb{Z}\right)))) \Rightarrow (\operatorname{H}\left(A\right) = \operatorname{H}\left(A'\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-2026-problem-12-affine-invariance` (proved) by `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-2026-problem-12-affine-invariance","declaration_gid":"D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Multiplication by s ≠ 0 followed by translation is injective. Injective images commute with intersections over the nonempty index type ℕ+. Distributing the h-fold sumset over the affine image changes its translation to h times t. Rewriting both sides through that image and reflecting equality by injectivity proves H A = H A′. The argument uses s ∉ {0, 1, −1} only to obtain s ≠ 0 and does not use either decrease premise.

## References

- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.AsymptoticallyStrictlyDecreasing`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.H`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.claim`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result`
