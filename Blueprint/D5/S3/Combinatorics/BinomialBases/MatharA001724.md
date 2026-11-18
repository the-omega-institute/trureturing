# Mathar's recurrence and D-finiteness for A001724

## Abstract

The signed first-kind Stirling sum defining OEIS A001724 satisfies Mathar's five-lag recurrence for every index at least five. Its ordinary rational formal generating series is annihilated by a nonzero sixth-order differential operator.

**Definition 1.1 (The full coefficient sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} ((-1)^{n + k} \cdot (\operatorname{choose}\left(k + 4, 4\right) : \mathbb{Z}) \cdot ((5 : \mathbb{Z}))^{k} \cdot \operatorname{s}\left(n + 4, k + 4\right))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001724.a` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829, A001722 and A001724*. URL: <https://oeis.org/A386829>.

*Commentary.*

This is Borislav Crstici's all-index formula in OEIS A001724, revision 43, https://raw.githubusercontent.com/oeis/oeisdata/87b54f574c5f92e16a7c0f5446596eb42715d0ff/seq/A001/A001724.seq. The canonical entry name is Generalized Stirling numbers [n+9,9]_5. The range contains both zero and n; the binomial coefficient is computed in the naturals and cast to the integers. The signed coefficient s is the existing MatharA001722.s: the coefficient of X^K in the integer falling product of length N, including the empty product. No recurrence or initial-value characterization is assumed.

**Definition 1.2 (Ordinary formal generating series).**

$$\forall n \in \mathbb{N},\; \operatorname{coeff}\left(n, O\right) = (\operatorname{a}\left(n\right) : \mathbb{Q})$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001724.O` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829, A001722 and A001724*. URL: <https://oeis.org/A386829>.

*Commentary.*

O is the ordinary formal power series whose nth coefficient is a(n) cast to the rationals. It is not an exponential generating series, and no convergence assertion is involved.

**Definition 1.3 (Recurrence and the ordinary interpretation).**

$$claim \Leftrightarrow ((\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (\operatorname{a}\left(n\right) + 5 \cdot \left(-(n : \mathbb{Z}) - 6\right) \cdot \operatorname{a}\left(n - 1\right) + 5 \cdot \left(2 \cdot ((n : \mathbb{Z}))^{2} + 22 \cdot (n : \mathbb{Z}) + 61\right) \cdot \operatorname{a}\left(n - 2\right) - 5 \cdot \left((n : \mathbb{Z}) + 5\right) \cdot \left(2 \cdot ((n : \mathbb{Z}))^{2} + 20 \cdot (n : \mathbb{Z}) + 51\right) \cdot \operatorname{a}\left(n - 3\right) + \left(5 \cdot ((n : \mathbb{Z}))^{4} + 90 \cdot ((n : \mathbb{Z}))^{3} + 610 \cdot ((n : \mathbb{Z}))^{2} + 1845 \cdot (n : \mathbb{Z}) + 2101\right) \cdot \operatorname{a}\left(n - 4\right) - ((n : \mathbb{Z}) + 4)^{5} \cdot \operatorname{a}\left(n - 5\right) = 0)) \land (\exists r \in \mathbb{N},\; \exists p \in \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right),\; (\exists j \in \mathbb{N},\; (j \le r) \land (\operatorname{p}\left(j\right) \ne 0)) \land (\sum_{j \in \operatorname{range}\left(r + 1\right)} (\operatorname{inclusion}\left(\operatorname{p}\left(j\right)\right) \cdot \operatorname{iterate}\left(D, j, O\right)) = 0)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MatharA001724.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829, A001722 and A001724*. URL: <https://oeis.org/A386829>.

*Commentary.*

The first assertion is Mathar's recurrence in the formula field of OEIS A001724, revision 43. Every n at least five is included; this onset is an explicit interpretation, not a bound stated in the quoted source. Subtraction in the subscripts is natural subtraction; n is cast to the integers before computing the polynomial coefficients. The second assertion requires a homogeneous polynomial-coefficient differential equation for the same full O, with at least one nonzero coefficient polynomial. The inclusion is the canonical map from rational polynomials to rational formal power series; D is formal differentiation, and its zeroth iterate is the identity.

**Theorem 1.4 (Recurrence and a homogeneous annihilator).**

$$(\forall n \in \mathbb{N},\; 5 \le n \Rightarrow (\operatorname{a}\left(n\right) + 5 \cdot \left(-(n : \mathbb{Z}) - 6\right) \cdot \operatorname{a}\left(n - 1\right) + 5 \cdot \left(2 \cdot ((n : \mathbb{Z}))^{2} + 22 \cdot (n : \mathbb{Z}) + 61\right) \cdot \operatorname{a}\left(n - 2\right) - 5 \cdot \left((n : \mathbb{Z}) + 5\right) \cdot \left(2 \cdot ((n : \mathbb{Z}))^{2} + 20 \cdot (n : \mathbb{Z}) + 51\right) \cdot \operatorname{a}\left(n - 3\right) + \left(5 \cdot ((n : \mathbb{Z}))^{4} + 90 \cdot ((n : \mathbb{Z}))^{3} + 610 \cdot ((n : \mathbb{Z}))^{2} + 1845 \cdot (n : \mathbb{Z}) + 2101\right) \cdot \operatorname{a}\left(n - 4\right) - ((n : \mathbb{Z}) + 4)^{5} \cdot \operatorname{a}\left(n - 5\right) = 0)) \land (\exists r \in \mathbb{N},\; \exists p \in \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right),\; (\exists j \in \mathbb{N},\; (j \le r) \land (\operatorname{p}\left(j\right) \ne 0)) \land (\sum_{j \in \operatorname{range}\left(r + 1\right)} (\operatorname{inclusion}\left(\operatorname{p}\left(j\right)\right) \cdot \operatorname{iterate}\left(D, j, O\right)) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MatharA001724.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a001724-recurrence-dfinite` (proved) by `D5/S3/Combinatorics/BinomialBases/MatharA001724.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a001724-recurrence-dfinite","declaration_gid":"D5/S3/Combinatorics/BinomialBases/MatharA001724.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Seiichi Manyama; Borislav Crstici (2026). *Mathar recurrence and D-finiteness conjectures: OEIS A386829, A001722 and A001724*. URL: <https://oeis.org/A386829>.

*Commentary.*

Let B(n)=(-1)^n times the Taylor translate at -5 of the falling product of length n+4. The Hasse derivative formula identifies its fourth coefficient with the full signed sum. The next falling-product factor gives B(n+1)=B(n)(n+9-X). The five-step linear combination with coefficients -(m+9)^5, 5m^4+190m^3+2710m^2+17195m+40951, -10m^3-300m^2-3005m-10050, 10m^2+210m+1105, -5m-55, 1 equals -X^5 B(m). Taking coefficient four gives the recurrence at n=m+5. For the ordinary series the order-six annihilator has coefficients p(0)=-35+1130X-15480X^2+105124X^3-295245X^4; p(1)=1-45X+1045X^2-13860X^3+99631X^4-304755X^5; p(2)=-5X^2+200X^3-3525X^4+30960X^5-111301X^6; p(3)=10X^4-330X^5+4115X^6-18890X^7; p(4)=-10X^6+240X^7-1600X^8; p(5)=5X^8-65X^9; p(6)=-X^10. Higher coefficient polynomials are zero. Coefficient extraction gives the recurrence multiplied by n+1. Boundary coefficients use a(0)=1, a(1)=35, a(2)=835, a(3)=17360, a(4)=342769. The leading polynomial -X^10 is nonzero. Mathar's wording does not specify ordinary versus exponential series. This canonical statement records the ordinary interpretation; it does not identify that interpretation with a verbatim source specification and does not include the separate exponential-series strengthening. Roberto Blanco Gómez, Proofs and corrections of 306 conjectures in the OEIS, DOI 10.5281/zenodo.23112421, Proposition 7.39 (English PDF p. 33), supplies the exact recurrence and an EGF operator conditional on Jovovic's logarithmic EGF formula. The record publication date is 2026-10-02; the PDF identifies itself as Version 6, dated 2026-10-03. Its assumed equality between that formula's coefficients and the literal signed sum is not authenticated. The present proof instead derives recurrence and ordinary D-finiteness directly from the signed sum; it does not prove that EGF identity. Separate D-finiteness statements, including the transient exponential check, do not imply equality with Jovovic's formula. The shared literature note and problem dossier retain the precise conditional-admission and unread-source limits; no first-solution or worldwide-novelty claim follows.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001724.O`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001724.a`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001724.claim`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MatharA001724.result`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MatharA001722](MatharA001722.md)
