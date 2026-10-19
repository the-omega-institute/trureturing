# Hanna's Bilateral Reversion Parity

## Abstract

Pairing bilateral Laurent summands proves the evenness conjecture for OEIS A379202.

P. D. Hanna's OEIS A379202 states: "G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1)." Its Comments section states: "Conjecture: a(n) is even for n > 1." The entry has offset 1 and begins 1, 4, 20, 122, 850. OEIS entries have named sections rather than page numbers.

Integer powers and inversion take place in LaurentSeries over the rationals. The natural index j selects the Laurent coefficient j-1. For A=X+… the nonnegative summand n has order at least n, and the summand -m has order m²-2m. Thus the finite window in bilateralSum contains every contributing summand. The type annotations on casts distinguish natural and integer indices.

**Definition 1.1 (The Laurent summand).**

$$\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \forall (n: \mathbb{Z}), \operatorname{term}\left(A, n\right) = (A: \operatorname{LaurentSeries}\left(\mathbb{Q}\right))^{n} \cdot ((A: \operatorname{LaurentSeries}\left(\mathbb{Q}\right))^{n} + 2)^{n + 1}$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.term` (`✓ std3`).

*Citation.* P. D. Hanna (2024). *OEIS A379202, a bilateral Laurent generating equation*. URL: <https://oeis.org/A379202>.

*Commentary.*

The summand in the entry's Name section, quoted above, uses the integer exponents n and n+1 without replacing inversion by power-series division.

**Definition 1.2 (The bilateral Laurent sum).**

$$\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{bilateralSum}\left(A\right) = \operatorname{HahnSeries}.\operatorname{single}\left((-(1): \mathbb{Z}), (1: \mathbb{Q})\right) \cdot \operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, \operatorname{PowerSeries}.\operatorname{mk}\left((\operatorname{fun} (j: \mathbb{N}) \mapsto \sum_{n \in \operatorname{Finset}.\operatorname{Icc}\left(-((j: \mathbb{Z})) - 2, (j: \mathbb{Z}) + 2\right)} \operatorname{HahnSeries}.\operatorname{coeff}\left(\operatorname{term}\left(A, n\right), (j: \mathbb{Z}) - 1\right))\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.bilateralSum` (`✓ std3`).

*Citation.* P. D. Hanna (2024). *OEIS A379202, a bilateral Laurent generating equation*. URL: <https://oeis.org/A379202>.

*Commentary.*

The Name section's "Sum_{n=-oo..+oo}" is interpreted coefficientwise. Multiplication by single(-1,1) shifts the constructed series down one degree. The coefficient of degree j-1 is summed over integers from -j-2 to j+2, inclusive.

**Definition 1.3 (The generating equation).**

$$\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsGF}\left(A\right)) \iff ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{PowerSeries}.\operatorname{coeff}\left(1, A\right) = 1) \land ((((X: \operatorname{PowerSeries}\left(\mathbb{Q}\right)): \operatorname{LaurentSeries}\left(\mathbb{Q}\right)))^{-1} = \operatorname{bilateralSum}\left(A\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.IsGF` (`✓ std3`).

*Citation.* P. D. Hanna (2024). *OEIS A379202, a bilateral Laurent generating equation*. URL: <https://oeis.org/A379202>.

*Commentary.*

"G.f. A(x) satisfies 1/x = Sum_{n=-oo..+oo} A(x)^n * (A(x)^n + 2)^(n+1)." This is the Name section of A379202. Offset 1 and the first entry 1 give constantCoeff A=0 and coeff 1 A=1. The coefficient a(n) is coeff n A.

**Definition 1.4 (The evenness conjecture).**

$$(claim) \iff ((\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsGF}\left(A\right)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsGF}\left(A\right)) \implies (\forall (n: \mathbb{N}), (1 < n) \implies (\exists (z: \mathbb{Z}), (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land (\operatorname{Even}\left(z\right))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.claim` (`✓ std3`).

*Citation.* P. D. Hanna (2024). *OEIS A379202, a bilateral Laurent generating equation*. URL: <https://oeis.org/A379202>.

*Commentary.*

"Conjecture: a(n) is even for n > 1." (A379202, Comments section; no page number.) The formula asserts existence of the rational generating series and, for every such series and every natural n>1, an integer coefficient z that is even. Even is Mathlib's integer parity predicate.

**Theorem 1.5 (Proof of the evenness conjecture).**

$$(\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsGF}\left(A\right)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsGF}\left(A\right)) \implies (\forall (n: \mathbb{N}), (1 < n) \implies (\exists (z: \mathbb{Z}), (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land (\operatorname{Even}\left(z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. D. Hanna (2024). *OEIS A379202, a bilateral Laurent generating equation*. URL: <https://oeis.org/A379202>.

*Commentary.*

Isolate the summand n=-1. Pair n=k with n=-k-2 for every natural k. The latter folds to A^(k(k+2)) times the (k+1)st power of the inverse of 1+2A^(k+2). Both members reduce to A^(k(k+2)) modulo two, so each pair vanishes. The normalized integer series T therefore reduces to 1. The series B=X/T has zero constant coefficient and linear coefficient 1; its integral compositional inverse reduces to X modulo two. Laurent-series normalization identifies every solution of the displayed equation with this inverse over the rationals, proving integrality and evenness for n>1.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.bilateralSum`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaBilateralReversionParity.term`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralProductModFour](../Bilateral/BilateralProductModFour.md)
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
- Dependency: [D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour](../Residue/QuotientThetaCompositionModFour.md)
