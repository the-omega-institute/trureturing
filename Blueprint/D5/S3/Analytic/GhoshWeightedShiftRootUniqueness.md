# A unique root of the weighted-shift polynomial

## Abstract

For positive real s and t and zero less than q less than one, the Ghosh-Birbonshi-Ojha polynomial has a unique root between one third and one.

**Definition 1.1 (The polynomial).**

$$\forall s,t,q,z:\mathbb{R}, g_{s,t,q}\left(z\right)=t\cdot q^{7}\cdot z^{8}+q^{6}\cdot \left(t\cdot q-1\right)\cdot z^{7}+3\cdot q^{5}\cdot \left(q-s\right)\cdot z^{6}+5\cdot q^{4}\cdot \left(s\cdot q-1\right)\cdot z^{5}+q^{3}\cdot \left(7\cdot q-9\cdot t\right)\cdot z^{4}+7\cdot q^{2}\cdot \left(t\cdot q-1\right)\cdot z^{3}+5\cdot q\cdot \left(q-s\right)\cdot z^{2}+3\cdot \left(s\cdot q-1\right)\cdot z+1$$

*Formalization.* `D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.g` (`✓ std3`).

*Citation.* Arobinda Ghosh, Riddhick Birbonshi, Sarita Ojha (2026). *On the numerical radius of a class of weighted shift operators*. URL: <https://arxiv.org/abs/2608.17486v1>.

*Commentary.*

For real parameters s, t and q, this is the degree-eight polynomial g in Section 2 of Ghosh, Birbonshi and Ojha. Its definition is valid for every real z; the root theorem below uses positive s and t and q strictly between zero and one.

**Theorem 1.2 (Existence and uniqueness in the open interval).**

$$\forall s,t,q:\mathbb{R}, \left(0<s \land 0<t \land 0<q \land q<1\right)\implies \exists! z:\mathbb{R}, \left(\frac{1}{3}<z \land z<1 \land g_{s,t,q}\left(z\right)=0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghosh-birbonshi-ojha-2026-weighted-shift-root-uniqueness` (proved) by `D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghosh-birbonshi-ojha-2026-weighted-shift-root-uniqueness","declaration_gid":"D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arobinda Ghosh, Riddhick Birbonshi, Sarita Ojha (2026). *On the numerical radius of a class of weighted shift operators*. URL: <https://arxiv.org/abs/2608.17486v1>.

*Commentary.*

For every pair of positive real parameters s and t and every real q strictly between zero and one, exactly one real z lies strictly between one third and one and makes the polynomial zero.

The value at one third is positive and the value at one is negative, so continuity gives an interior root. At each interior root, an exact polynomial identity gives a strictly negative derivative. The cubic term in that identity is positive by its endpoint values and chord decomposition on zero less than c less than z squared, where c equals q squared times z squared.

If two roots were ordered u less than v, the differential fence with constant boundary zero would keep g nonpositive between them. A negative derivative at v forces positive values immediately to its left, a contradiction. This conclusion concerns the scalar polynomial root; it does not identify an operator numerical radius.

## References

- Truth anchor: `D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.g`
- Truth anchor: `D5/S3/Analytic/GhoshWeightedShiftRootUniqueness.result`
