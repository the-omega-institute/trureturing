# A negative answer to the finite-subindex question

## Abstract

A rank-five commutative ring has no finite subset that computes all its Knutson indices.

**Definition 1.1 (Regular elements).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall \alpha: R \to+* \mathbb{Z}, \forall r: R, \operatorname{IsRegularElement}\left(\alpha, r\right) = ((\alpha\left(r\right) \ne 0) \land (\forall x: R, x \cdot r = \operatorname{SMul.smul}\left(\alpha\left(x\right), r\right)))$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.IsRegularElement` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Section 2, p. 4794: “We call an element r ∈ R regular if α(r) ≠ 0 and x·r = α(x) r for all x ∈ R.” Here R is a commutative ring, α is a unital ring homomorphism to ℤ, and the right-hand side uses integer scalar multiplication. This meaning of regular is specific to the source.

**Definition 1.2 (The Knutson index).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall r: R, \forall x: R, \operatorname{knutsonIndex}\left(r, x\right) = \operatorname{sInf}\left(\{m: \mathbb{N} \mid (0 < m) \land (\exists y: R, y \cdot x = \operatorname{SMul.smul}\left((m: \mathbb{Z}), r\right))\}\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.knutsonIndex` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Definition 2.1, p. 4794: “The Knutson Index 𝒦_r(x) of an element x ∈ R with respect to a regular element r ∈ R is the non-negative integer m such that Rx ∩ ℤr = mℤr.” The display gives the least positive coefficient of r in Rx, and zero if no positive coefficient occurs; sInf on ℕ has that empty-set value. For regular r this agrees with the generator in the quoted definition, since r has infinite additive order and the coefficient set is an ideal of ℤ. The natural coefficient is explicitly cast to ℤ before scalar multiplication.

**Definition 1.3 (Eligible multipliers).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall r: R, \forall S: \operatorname{Finset}\left(R\right), \forall x: R, \operatorname{eligible}\left(r, S, x\right) = \operatorname{Finset.filter}\left((\lambda s: R, \exists m: \mathbb{Z}, s \cdot x = \operatorname{SMul.smul}\left(m, r\right)), S\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.eligible` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Definition 2.2, p. 4794: “Let S ⊂ R be a subset, and for any x ∈ R define S(x) = {s ∈ S: s·x ∈ ℤr}.” Finset represents the finite subset S. Membership in ℤr is the existence of an integer m with s * x = m • r.

**Definition 1.4 (The integer coefficient).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall r: R, \forall s: R, \forall x: R, \operatorname{eligibleIndex}\left(r, s, x\right) = (\operatorname{if} h: (\exists m: \mathbb{Z}, s \cdot x = \operatorname{SMul.smul}\left(m, r\right)) \operatorname{then} \operatorname{Exists.choose}\left(h\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.eligibleIndex` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Definition 2.2, p. 4794, states: “Associated to S(x) we also set Ind(x) = {m ∈ ℤ: s·x = m·r for s ∈ S(x)}.” The displayed dependent conditional chooses that integer when it exists and returns zero otherwise. For a regular r it is unique, because applying α to m • r and using α(r) ≠ 0 proves injectivity of the integer coefficient. The variable h is the existence proof used by Exists.choose.

**Definition 1.5 (The finite-set subindex).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall r: R, \forall S: \operatorname{Finset}\left(R\right), \forall x: R, \operatorname{knutsonSubindex}\left(r, S, x\right) = \operatorname{ite}\left(\operatorname{Finset.Nonempty}\left(\operatorname{eligible}\left(r, S, x\right)\right), ((\operatorname{Finset.gcd}\left(\operatorname{eligible}\left(r, S, x\right), (\lambda s: R, \operatorname{Int.natAbs}\left(\operatorname{eligibleIndex}\left(r, s, x\right)\right))\right): \mathbb{N}): \mathbb{N}^{\infty}), \infty\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.knutsonSubindex` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Definition 2.2, p. 4794, states: “Define the Knutson S-subindex of x ∈ R with respect to the regular element r ∈ R as 𝒦_r^S(x) := gcd(Ind(x)).” It adds: “By convention, if S(x) = ∅ then we set 𝒦_r^S(x) = ∞.” The gcd is taken on the natural absolute values of all eligible integer coefficients and cast to ℕ∞. An empty eligible set gives ⊤, the infinity of ℕ∞. The finite-set gcd includes zero coefficients without changing a nonzero gcd.

**Definition 1.6 (Question 2.5).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], [\operatorname{Algebra.FiniteType}\left(\mathbb{Z}, R\right)], \forall \alpha: R \to+* \mathbb{Z}, \forall r: R, (\operatorname{IsRegularElement}\left(\alpha, r\right)) \Rightarrow (\exists S: \operatorname{Finset}\left(R\right), \forall x: R, (\operatorname{knutsonIndex}\left(r, x\right): \mathbb{N}^{\infty}) = \operatorname{knutsonSubindex}\left(r, S, x\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.claim` (`✓ std3`).

*Citation.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Question 2.5, p. 4795: “Does there exist a finite subset S ⊂ R such that for all x ∈ R we have 𝒦_r(x) = 𝒦_r^S(x)?” Section 2, p. 4794, begins: “Let R be a finitely generated commutative ring. Suppose that R is equipped with a ring homomorphism α: R → ℤ.” The proposition is the affirmative answer for every ring in that setting and every regular r. Algebra.FiniteType ℤ R expresses finite generation as a commutative ring. Both instance parameters are displayed anonymously. The ordinary index is cast from ℕ to ℕ∞ for the comparison.

**Theorem 1.7 (No finite subset suffices in general).**

$$\neg(\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], [\operatorname{Algebra.FiniteType}\left(\mathbb{Z}, R\right)], \forall \alpha: R \to+* \mathbb{Z}, \forall r: R, (\operatorname{IsRegularElement}\left(\alpha, r\right)) \Rightarrow (\exists S: \operatorname{Finset}\left(R\right), \forall x: R, (\operatorname{knutsonIndex}\left(r, x\right): \mathbb{N}^{\infty}) = \operatorname{knutsonSubindex}\left(r, S, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnston-martin-duro-rumynin-2024-knutson-index-question-2-5` (refuted) by `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnston-martin-duro-rumynin-2024-knutson-index-question-2-5","declaration_gid":"D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin (2025). *Global Representation Ring and Knutson Index*. DOI: [10.1080/00927872.2025.2498055](https://doi.org/10.1080/00927872.2025.2498055). URL: <https://arxiv.org/abs/2403.18498v6>.

*Commentary.*

Use a ring whose elements are integer tuples (d,a,b,f,t), with augmentation d + 2a + 2b + 4t. Its multiplication is the coordinate multiplication of the fiber product of ℤ and ℤ[u,v]/(u²,v²) over ℤ/4, where u and v map to 2. The tuple r = (0,0,0,0,1) is regular and has augmentation 4. For every integer k, X(k) = (0,1,2k,0,−k) and Y(k) = (0,1,−2k,0,k) multiply to r, so X(k) has Knutson index one. Given a finite S, choose k = 1 + ∑(s ∈ S) |s.b|. Eligibility of s forces s.d = 0 and s.b = −2k s.a. The bound on |s.b| forces s.a = s.b = 0, and the coefficient of r is then 2s.t, an even integer. The subindex is therefore divisible by two or infinite, so it differs from one. Proposition 2.6 still gives a finite subset for reduced rings. The source states that the rings in its subsequent applications embed in finite products of ℂ and hence are reduced; those applications retain that hypothesis.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.IsRegularElement`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.eligible`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.eligibleIndex`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.knutsonIndex`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.knutsonSubindex`
- Truth anchor: `D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation.result`
