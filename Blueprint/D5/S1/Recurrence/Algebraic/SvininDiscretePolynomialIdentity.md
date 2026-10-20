# Svinin's Discrete-Polynomial Identity

## Abstract

Svinin's discrete-polynomial convolution identity holds over every commutative ring.

The field T(i) in Svinin's paper is an arbitrary function u from the integers to a commutative ring R. Section 3 fixes (h,n)=(1,1). The finite maps lambda:Fin(r) to Fin(Int.toNat(s)) enumerate the increasing or weakly increasing tuples, with indices starting at zero. A product over Fin(0) is one. For positive degree a nonpositive subscript gives an empty sum. Natural subtraction in degree indices and finite-range lengths is truncated at zero; subscript and lattice arithmetic takes place in the integers. The displayed integer casts include the coercions from Fin through val.

**Definition 1.1 (Strictly increasing tuple polynomials).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall u: \mathbb{Z} \to R, \forall r: \mathbb{N}, \forall s: \mathbb{Z}, \forall i: \mathbb{Z}, \operatorname{T}\left(u, r, s, i\right) = \sum_{lam \in \operatorname{Finset}.\operatorname{filter}\left(\operatorname{StrictMono}, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(r\right) \to \operatorname{Fin}\left(\operatorname{Int}.\operatorname{toNat}\left(s\right)\right))\right))\right)} (\prod_{a: \operatorname{Fin}\left(r\right)} u\left(i + (\operatorname{val}\left(lam\left(a\right)\right): \mathbb{Z}) + (\operatorname{val}\left(a\right): \mathbb{Z})\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.T` (`✓ std3`).

*Citation.* A. K. Svinin (2015). *On integrals for some class of ordinary difference equations admitting a Lax pair representation*. DOI: [10.1088/1751-8113/49/9/095201](https://doi.org/10.1088/1751-8113/49/9/095201). URL: <https://arxiv.org/abs/1505.06394v2>.

*Commentary.*

Page 3, Eq. (4): "T^r_s(i) := Σ_{{λ_j}∈D_{r,s}} T(i + λ_1h)T(i + λ_2h + n) ⋯ T(i + λ_rh + (r − 1)n) with D_{r,s} := {λ_j : 0 ≤ λ_1 < ⋯ < λ_r ≤ s − 1} … we put T^0_s(i) ≡ 1." Here h=n=1, u is the paper's field T, and a:Fin(r) is its factor index minus one.

**Definition 1.2 (Weakly increasing tuple polynomials).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall u: \mathbb{Z} \to R, \forall r: \mathbb{N}, \forall s: \mathbb{Z}, \forall i: \mathbb{Z}, \operatorname{S}\left(u, r, s, i\right) = \sum_{lam \in \operatorname{Finset}.\operatorname{filter}\left(\operatorname{Monotone}, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(r\right) \to \operatorname{Fin}\left(\operatorname{Int}.\operatorname{toNat}\left(s\right)\right))\right))\right)} (\prod_{a: \operatorname{Fin}\left(r\right)} u\left(i + (\operatorname{val}\left(lam\left(a\right)\right): \mathbb{Z}) + ((r: \mathbb{Z}) - 1 - (\operatorname{val}\left(a\right): \mathbb{Z}))\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.S` (`✓ std3`).

*Citation.* A. K. Svinin (2015). *On integrals for some class of ordinary difference equations admitting a Lax pair representation*. DOI: [10.1088/1751-8113/49/9/095201](https://doi.org/10.1088/1751-8113/49/9/095201). URL: <https://arxiv.org/abs/1505.06394v2>.

*Commentary.*

Page 5, Section 2.3: "S^r_s(i) := Σ_{{λ_j}∈B_{r,s}} T(i + λ_1h + (k − 1)n) ⋯ T(i + λ_{r−1}h + n)T(i + λ_rh) … B_{r,s} ≡ {λ_j : 0 ≤ λ_1 ≤ ⋯ ≤ λ_r ≤ s − 1}." The printed k in the first offset is read as r, as determined by the displayed factor pattern and recurrences (10)–(11). With h=n=1 the offset at zero-based factor a is r−1−a in the integers.

**Definition 1.3 (The alternating binary operation).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall F: \mathbb{N} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to R\right)\right), \forall G: \mathbb{N} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to R\right)\right), \forall r: \mathbb{N}, \forall s: \mathbb{Z}, \forall i: \mathbb{Z}, \operatorname{bracket}\left(F, G, r, s, i\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(r + 1\right)} (\left(-1\right)^{j} \cdot F\left(r - j, s + (j: \mathbb{Z}), i\right) \cdot G\left(j, s - (r: \mathbb{Z}) + (j: \mathbb{Z}), i + (r: \mathbb{Z}) - (j: \mathbb{Z})\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.bracket` (`✓ std3`).

*Citation.* A. K. Svinin (2015). *On integrals for some class of ordinary difference equations admitting a Lax pair representation*. DOI: [10.1088/1751-8113/49/9/095201](https://doi.org/10.1088/1751-8113/49/9/095201). URL: <https://arxiv.org/abs/1505.06394v2>.

*Commentary.*

Page 12, Section 3.4: "⟨F, G⟩^r_s(i) = Σ_{j=0}^{r} (−1)^j F^{r−j}_{s+j}(i) G^j_{s−r+j}(i + r − j). Remark that in this formula we put F^r_s(i) ≡ 0 for s ≤ 0." The sum uses Finset.range(r+1). For the polynomial families T and S, the zero-degree value stays one, including at nonpositive subscripts, while positive degrees vanish there.

**Definition 1.4 (Conjecture 1, Eq. (48)).**

$$\operatorname{claim} \iff (\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall u: \mathbb{Z} \to R, \forall r: \mathbb{N}, (1 \le r) \implies (\forall s: \mathbb{Z}, ((r: \mathbb{Z}) - 1 \le s) \implies (\forall i: \mathbb{Z}, \operatorname{bracket}\left(\operatorname{S}\left(u\right), \operatorname{T}\left(u\right), r, s, i\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(r - 1\right)} (\left(-1\right)^{j} \cdot u\left(i + (r: \mathbb{Z}) - (j: \mathbb{Z}) - 2\right) \cdot u\left(i + s + (j: \mathbb{Z})\right) \cdot \operatorname{S}\left(u, r - j - 2, s + (j: \mathbb{Z}) + 2, i\right) \cdot \operatorname{T}\left(u, j, s - (r: \mathbb{Z}) + (j: \mathbb{Z}), i + (r: \mathbb{Z}) - (j: \mathbb{Z})\right)))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.claim` (`✓ std3`).

*Citation.* A. K. Svinin (2015). *On integrals for some class of ordinary difference equations admitting a Lax pair representation*. DOI: [10.1088/1751-8113/49/9/095201](https://doi.org/10.1088/1751-8113/49/9/095201). URL: <https://arxiv.org/abs/1505.06394v2>.

*Commentary.*

Page 12, Conjecture 1: "The relations ⟨S, T⟩^r_s(i) = Σ_{j=0}^{r−2} (−1)^j T(i + r − j − 2)T(i + s + j) × S^{r−j−2}_{s+j+2}(i) T^j_{s−r+j}(i + r − j), ∀ s ≥ r − 1 (48) are identities. Unfortunately, by now we can prove this conjecture only for r = 1, 2, 3." The formula quantifies every commutative ring, every field u, every natural r≥1, and all integer s≥r−1 and i. For r=1 the right side is empty. Completeness of the literature search is ASSUMED-UNVERIFIED.

**Theorem 1.5 (The identity in every degree).**

$$\forall R: \operatorname{Type}, [\operatorname{CommRing}\left(R\right)], \forall u: \mathbb{Z} \to R, \forall r: \mathbb{N}, (1 \le r) \implies (\forall s: \mathbb{Z}, ((r: \mathbb{Z}) - 1 \le s) \implies (\forall i: \mathbb{Z}, \operatorname{bracket}\left(\operatorname{S}\left(u\right), \operatorname{T}\left(u\right), r, s, i\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(r - 1\right)} (\left(-1\right)^{j} \cdot u\left(i + (r: \mathbb{Z}) - (j: \mathbb{Z}) - 2\right) \cdot u\left(i + s + (j: \mathbb{Z})\right) \cdot \operatorname{S}\left(u, r - j - 2, s + (j: \mathbb{Z}) + 2, i\right) \cdot \operatorname{T}\left(u, j, s - (r: \mathbb{Z}) + (j: \mathbb{Z}), i + (r: \mathbb{Z}) - (j: \mathbb{Z})\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/svinin-2015-discrete-polynomial-identity` (proved) by `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"svinin-2015-discrete-polynomial-identity","declaration_gid":"D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. K. Svinin (2015). *On integrals for some class of ordinary difference equations admitting a Lax pair representation*. DOI: [10.1088/1751-8113/49/9/095201](https://doi.org/10.1088/1751-8113/49/9/095201). URL: <https://arxiv.org/abs/1505.06394v2>.

*Commentary.*

The weighted tuple partitions give the left Pascal recurrences; reversal gives their right counterparts. Subtracting the quadratic correction from S produces a polynomial Q whose convolution with T is invariant under (s,i)↦(s−1,i+1). At s=r−1 all positive-degree T factors vanish. The remaining Q depends on a finite window and is invariant under translation for every field. A field cut off beyond that window agrees with zero on a disjoint translated window, so Q equals zero. Induction on s−r+1 and expansion of the correction prove the displayed identity. No division or nonzero field value is required; commutative rings with zero divisors are included. This proves the prerequisite used by the paper's later difference-equation equivalences for (h,n)=(1,1); those equivalences and their other hypotheses are separate statements. General coprime (h,n) and noncommutative coefficients remain open here.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.S`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.T`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.bracket`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result`
