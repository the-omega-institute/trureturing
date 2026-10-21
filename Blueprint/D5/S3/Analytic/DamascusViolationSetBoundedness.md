# Boundedness of the Damascus violation sets

## Abstract

The positive product-one Damascus violation sets have a complete boundedness classification.

**Definition 1.1 (The Damascus summand).**

$$\forall (n : \mathbb{N}), \forall (x : \mathbb{R}), \operatorname{term}\left(n, x\right) = \frac{x^{n} - 1}{x^{n + 1} + 1}$$

*Formalization.* `D5/S3/Analytic/DamascusViolationSetBoundedness.term` (`✓ std3`).

*Citation.* Chanatip Sujsuntinukul and Christophe Chesneau (2026). *Variants of the Damascus inequality*. DOI: [10.1007/s11139-026-01345-1](https://doi.org/10.1007/s11139-026-01345-1). URL: <https://arxiv.org/abs/2601.00916v4>.

*Commentary.*

Inequality (1), page 2: “S_n^m(x₁, …, x_m) := Σ_{j=1}^m (x_jⁿ − 1)/(x_j^{n+1} + 1) ⩽ 0”. The function term is its real summand, with natural exponent n. Real division is total; the denominator is positive at every positive x.

**Definition 1.2 (Positive tuples with product one).**

$$\forall (m : \mathbb{N}), \operatorname{H}\left(m\right) = \{x : \operatorname{Fin}\left(m\right) \to \mathbb{R} | ((\forall (j : \operatorname{Fin}\left(m\right)), 0 < \operatorname{x}\left(j\right)) \land (\prod_{j : \operatorname{Fin}\left(m\right)} \operatorname{x}\left(j\right) = 1))\}$$

*Formalization.* `D5/S3/Analytic/DamascusViolationSetBoundedness.H` (`✓ std3`).

*Citation.* Chanatip Sujsuntinukul and Christophe Chesneau (2026). *Variants of the Damascus inequality*. DOI: [10.1007/s11139-026-01345-1](https://doi.org/10.1007/s11139-026-01345-1). URL: <https://arxiv.org/abs/2601.00916v4>.

*Commentary.*

Page 2 defines “H_m := {(x₁, …, x_m) ∈ (0, +∞)^m : ∏_{j=1}^m x_j = 1}”. Coordinates are functions Fin m → ℝ, indexed from zero in Lean; each coordinate occurs once in the product.

**Definition 1.3 (The strict violation set).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \operatorname{I}\left(n, m\right) = \{x : \operatorname{Fin}\left(m\right) \to \mathbb{R} | ((x \in \operatorname{H}\left(m\right)) \land (0 < \sum_{j : \operatorname{Fin}\left(m\right)} \operatorname{term}\left(n, \operatorname{x}\left(j\right)\right)))\}$$

*Formalization.* `D5/S3/Analytic/DamascusViolationSetBoundedness.I` (`✓ std3`).

*Citation.* Chanatip Sujsuntinukul and Christophe Chesneau (2026). *Variants of the Damascus inequality*. DOI: [10.1007/s11139-026-01345-1](https://doi.org/10.1007/s11139-026-01345-1). URL: <https://arxiv.org/abs/2601.00916v4>.

*Commentary.*

Section 5, page 13: “I_n^m := {(x₁, …, x_m) ∈ H_m : Σ_{j=1}^m (x_jⁿ − 1)/(x_j^{n+1} + 1) > 0}. For instance, we know that I_n^2 = ∅ for all n, and (1/2, 3/2, 4/3) ∈ I_n^3 for n ⩾ 5.” The function I uses the strict real inequality and the product-one set H, with a sum over Fin m.

**Definition 1.4 (The answer to the boundedness question).**

$$claim = (\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), (1 \le m) \Rightarrow ((1 \le n) \Rightarrow ((\operatorname{Bornology.IsBounded}\left(\operatorname{I}\left(n, m\right)\right)) \Leftrightarrow ((m \le 3) \lor (((m = 4) \land (n \le 4)) \lor (((m = 5) \lor (m = 6)) \land (n = 1)))))))$$

*Formalization.* `D5/S3/Analytic/DamascusViolationSetBoundedness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chanatip Sujsuntinukul and Christophe Chesneau (2026). *Variants of the Damascus inequality*. DOI: [10.1007/s11139-026-01345-1](https://doi.org/10.1007/s11139-026-01345-1). URL: <https://arxiv.org/abs/2601.00916v4>.

*Commentary.*

Section 5, page 19: “In addition to the above, it is natural to ask whether analogous structural properties hold for I_n^m when m is arbitrary. Can one prove or disprove that I_n^m (i) stays uniformly away from 1, (ii) is bounded, or (iii) forms an increasing family in n?” The source concludes: “Thus this question, together with question (iii), remains open.” The answer is quantified over positive natural dimensions and exponents. Boundedness uses Bornology.IsBounded on Fin m → ℝ. It holds precisely for m ≤ 3, for m = 4 with n ≤ 4, and for m = 5 or 6 with n = 1.

**Theorem 1.5 (The complete classification).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), (1 \le m) \Rightarrow ((1 \le n) \Rightarrow ((\operatorname{Bornology.IsBounded}\left(\operatorname{I}\left(n, m\right)\right)) \Leftrightarrow ((m \le 3) \lor (((m = 4) \land (n \le 4)) \lor (((m = 5) \lor (m = 6)) \land (n = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/DamascusViolationSetBoundedness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chanatip Sujsuntinukul and Christophe Chesneau (2026). *Variants of the Damascus inequality*. DOI: [10.1007/s11139-026-01345-1](https://doi.org/10.1007/s11139-026-01345-1). URL: <https://arxiv.org/abs/2601.00916v4>.

*Commentary.*

For a positive coordinate x the summand lies strictly above −1 and strictly below 1/x. For x ≤ 1, term(n,x) + 1 ≤ 2x. Uniform bounds strictly below 1, together with term(1,x) ≤ 5/24 and term(4,x) ≤ 4999/10000, give confinement in the stated cases. If a coordinate exceeds K^(m−1), the product-one identity forces another below 1/K; these two coordinates and the remaining m−2 scalar bounds make the sum negative. In the other cases the tuple (t, 1/(t r^k), r, …, r), k = m−2, has product one and a strictly positive sum for every t > 1. Use r = 2 for n ≤ 4 and r = 3/2 for n ≥ 5. At (m,n) = (5,2) the middle summands sum exactly to 1; the two other summands sum strictly above −1. Thus this equality case is unbounded as well. The source's nesting question and separation from coordinate-one planes in arbitrary dimension are separate questions.

## References

- Truth anchor: `D5/S3/Analytic/DamascusViolationSetBoundedness.H`
- Truth anchor: `D5/S3/Analytic/DamascusViolationSetBoundedness.I`
- Truth anchor: `D5/S3/Analytic/DamascusViolationSetBoundedness.claim`
- Truth anchor: `D5/S3/Analytic/DamascusViolationSetBoundedness.result`
- Truth anchor: `D5/S3/Analytic/DamascusViolationSetBoundedness.term`
