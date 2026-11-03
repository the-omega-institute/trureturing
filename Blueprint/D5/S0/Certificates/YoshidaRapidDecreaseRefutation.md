# Yoshida's Rapid-Decrease Question

## Abstract

A positive sequence satisfies Yoshida's rapid-decrease inequalities but its first Turan transform does not.

**Definition 1.1 (Rapid decrease).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; RapidlyDecreasing\left(a\right) = \left((\forall k \in \mathbb{N},\; 0 < a\left(k\right)) \land (\exists alpha \in \mathbb{R},\; (max\left(2, \frac{\operatorname{Real}.\operatorname{sqrt}\left(2\right)}{2} \cdot \left(1 + \operatorname{Real}.\operatorname{sqrt}\left(1 + a\left(1\right)\right)\right)\right) \le alpha) \land (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (a\left(k\right)^{2} \ge alpha^{2} \cdot ite\left((k:\mathbb{Z}) - 1 < 0, 0, a\left(\operatorname{Int}.\operatorname{toNat}\left((k:\mathbb{Z}) - 1\right)\right)\right) \cdot ite\left((k:\mathbb{Z}) + 1 < 0, 0, a\left(\operatorname{Int}.\operatorname{toNat}\left((k:\mathbb{Z}) + 1\right)\right)\right))))\right)$$

*Formalization.* `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.RapidlyDecreasing` (`✓ std3`).

*Citation.* Rintaro Yoshida (2010). *On some questions of Fisk and Brändén*. DOI: [10.48550/arXiv.1005.4218](https://doi.org/10.48550/arXiv.1005.4218). URL: <https://arxiv.org/abs/1005.4218v1>.

*Commentary.*

Definition 29 (p. 10): "A sequence of positive real numbers $\{s_{k}\}_{k=0}^{\infty}$ is called rapidly decreasing, if the sequence satisfies the following condition $\left(s_{k}\right)^{2}\geq\alpha^{2}s_{k - 1}s_{k + 1}$, for $\alpha\geq \max\{2,\frac{\sqrt{2}}{2}(1 + \sqrt{1 + s_{1}})\}$."

The sequence a has natural indices, all its terms are positive, and one real alpha satisfies the threshold and every inequality at k>=1.

**Definition 1.2 (The transformed coefficients).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \forall r \in \mathbb{N},\; \forall k \in \mathbb{N},\; sCoeff\left(a, r, k\right) = a\left(k\right)^{2} - ite\left((k:\mathbb{Z}) - (r:\mathbb{Z}) < 0, 0, a\left(\operatorname{Int}.\operatorname{toNat}\left((k:\mathbb{Z}) - (r:\mathbb{Z})\right)\right)\right) \cdot ite\left((k:\mathbb{Z}) + (r:\mathbb{Z}) < 0, 0, a\left(\operatorname{Int}.\operatorname{toNat}\left((k:\mathbb{Z}) + (r:\mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.sCoeff` (`✓ std3`).

*Citation.* Rintaro Yoshida (2010). *On some questions of Fisk and Brändén*. DOI: [10.48550/arXiv.1005.4218](https://doi.org/10.48550/arXiv.1005.4218). URL: <https://arxiv.org/abs/1005.4218v1>.

*Commentary.*

Open Problem 5 (p. 11) writes Sᵣ[f(x)]=∑ₖ₌₀∞ (aₖ²−aₖ₋ᵣaₖ₊ᵣ)xᵏ:=∑ₖ₌₀∞ bₖxᵏ. The function sCoeff(a,r) is the coefficient sequence of S_r[f]. Definition 8 (p. 3) sets "and aⱼ=0 if j∉{0,1,…,n}." Only negative indices are outside an infinite sequence. The conditional ite returns zero at negative indices and a(Int.toNat(j)) otherwise. Both k and r are natural numbers; the two shifted indices are cast to integers before subtraction and addition.

**Definition 1.3 (Open Problem 5).**

$$claim = \left((\exists a \in \mathbb{N} \to \mathbb{R},\; RapidlyDecreasing\left(a\right)) \land (\forall a \in \mathbb{N} \to \mathbb{R},\; (RapidlyDecreasing\left(a\right)) \Rightarrow (\forall r \in \mathbb{N},\; (1 \le r) \Rightarrow (RapidlyDecreasing\left(sCoeff\left(a, r\right)\right))))\right)$$

*Formalization.* `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.claim` (`✓ std3`).

*Citation.* Rintaro Yoshida (2010). *On some questions of Fisk and Brändén*. DOI: [10.48550/arXiv.1005.4218](https://doi.org/10.48550/arXiv.1005.4218). URL: <https://arxiv.org/abs/1005.4218v1>.

*Commentary.*

Open Problem 5 (p. 11): "Let $f\left(x\right) = \sum_{k=0}^{\infty}a_{k}x^{k}$ where $\{a_{k}\}_{k=0}^{\infty}$ is a rapidly decreasing sequence. If $S_{r}[f\left(x\right)]=\sum_{k=0}^{\infty}(\left(a_{k}\right)^{2} - a_{k - r}a_{k + r})x^{k}:=\sum_{k=0}^{\infty}b_{k}x^{k}$, is it true that $\{b_{k}\}_{k=0}^{\infty}$ is a rapidly decreasing sequence?"

A power series is represented by its coefficients a. The first conjunct asserts existence of such a sequence; the second asserts closure for every such sequence and every positive natural r. The predicate RapidlyDecreasing and the function sCoeff are expanded above.

**Theorem 1.4 (A negative answer).**

$$\neg ((\exists a \in \mathbb{N} \to \mathbb{R},\; RapidlyDecreasing\left(a\right)) \land (\forall a \in \mathbb{N} \to \mathbb{R},\; (RapidlyDecreasing\left(a\right)) \Rightarrow (\forall r \in \mathbb{N},\; (1 \le r) \Rightarrow (RapidlyDecreasing\left(sCoeff\left(a, r\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yoshida-rapid-decrease` (refuted) by `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yoshida-rapid-decrease","declaration_gid":"D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rintaro Yoshida (2010). *On some questions of Fisk and Brändén*. DOI: [10.48550/arXiv.1005.4218](https://doi.org/10.48550/arXiv.1005.4218). URL: <https://arxiv.org/abs/1005.4218v1>.

*Commentary.*

Take aₖ=48ᵏ/32^(k choose 2) and r=1. Every a_k is positive, a_0=1 and a_1=48. The adjacent identity aₖ₊₁²=32aₖaₖ₊₂ gives rapid decrease with alpha=4 sqrt(2). The first transformed coefficients are 1, 2232 and 5022. The output inequality at index 1 forces alpha squared to be at most 992. Its threshold forces alpha squared to be at least 1117+sqrt(2233), which is larger. This contradiction concerns the coefficient question; it asserts no failure of Laguerre-Polya membership.

## References

- Truth anchor: `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.RapidlyDecreasing`
- Truth anchor: `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.claim`
- Truth anchor: `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result`
- Truth anchor: `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.sCoeff`
