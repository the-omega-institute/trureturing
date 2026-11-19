# Hanna A381361: all terms are odd

## Abstract

Every exponential coefficient of Hanna's implicit rational series is an odd integer.

**Definition 1.1 (The implicit rational source series).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Leftrightarrow ((\operatorname{PowerSeries.constantCoeff}\left(A\right) = 1) \land (\exists I \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{PowerSeries.constantCoeff}\left(I\right) = 0) \land ((\operatorname{PowerSeries.derivative}\left(I\right) = \operatorname{HannaAbsoluteCubicCongruence.absSeries}\left((A^{2})^{-1}\right)) \land (A = \operatorname{PowerSeries.subst}\left(I, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)))))$$

*Formalization.* `D5/S1/Recurrence/Parity/HannaA381361AllOdd.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A381361: all terms are odd*. URL: <https://oeis.org/A381361/internal>.

*Commentary.*

OEIS A381361 revision 25, NAME field (no page number): “E.g.f. satisfies A(x) = exp( Integral abs(1/A(x)^2) dx ), where abs(F(x)) equals the series expansion formed by the unsigned coefficients in F(x).” The series A and I have rational coefficients. The primitive I has constant coefficient zero, A has constant coefficient one, and absSeries takes the absolute value of each ordinary coefficient. PowerSeries.subst takes I first and the rational exponential series second. All operations are formal.

**Definition 1.2 (The all-odd assertion).**

$$claim \Leftrightarrow ((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsSourceSeries}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{IntegralEGFComposition.eCoeff}\left(A, n\right) = (2: \mathbb{Q}) \cdot (z: \mathbb{Q}) + 1)))$$

*Formalization.* `D5/S1/Recurrence/Parity/HannaA381361AllOdd.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A381361: all terms are odd*. URL: <https://oeis.org/A381361/internal>.

*Commentary.*

OEIS A381361 revision 25, first COMMENTS line (no page number): “All terms appear to be odd.” The FORMULA field reads: “E.g.f. A(x) = Sum_{n>=0} a(n)*x^n/n! satisfies the following formulas.” The coefficient eCoeff A n is n! times PowerSeries.coeff n A. Existence is included, and every rational source solution has eCoeff A n = 2z+1 for an integer z at every natural index, including zero.

**Theorem 1.3 (Every term is an odd integer).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsSourceSeries}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{IntegralEGFComposition.eCoeff}\left(A, n\right) = (2: \mathbb{Q}) \cdot (z: \mathbb{Q}) + 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/HannaA381361AllOdd.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381361-hanna-all-odd` (proved) by `D5/S1/Recurrence/Parity/HannaA381361AllOdd.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381361-hanna-all-odd","declaration_gid":"D5/S1/Recurrence/Parity/HannaA381361AllOdd.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A381361: all terms are odd*. URL: <https://oeis.org/A381361/internal>.

*Commentary.*

The rational source series exists uniquely and its exponential coefficients are integers. In characteristic two every normalized Hurwitz square is the unit sequence; inversion and coefficientwise absolute value preserve this reduction. The derivative recurrence therefore gives a(n+1)=a(n) modulo two. Since a(0)=1, every term is odd. The claim concerns only this parity assertion; divisibility by five and elliptic or asymptotic formulas require separate arguments.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/HannaA381361AllOdd.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/HannaA381361AllOdd.claim`
- Truth anchor: `D5/S1/Recurrence/Parity/HannaA381361AllOdd.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaAbsoluteCubicCongruence](../Algebraic/HannaAbsoluteCubicCongruence.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree](ExponentialImplicitParityPeriodThree.md)
- Dependency: [D5/S1/Recurrence/Residue/HannaEGFMachinery](../Residue/HannaEGFMachinery.md)
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)
