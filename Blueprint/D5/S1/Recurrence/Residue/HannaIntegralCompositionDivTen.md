# Hanna's integral composition equation modulo ten

## Abstract

The rational exponential generating series of A277403 has integral coefficients divisible by ten above index two.

Exponential coefficients are eCoeff(A,n)=n! times the ordinary coefficient of A. The zero integration constant and A(0)=0 agree with the displayed example in OEIS A277403. All series are formal power series over the rationals.

**Definition 1.1 (The source equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall G \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsSolution}\left(A, G\right)) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(G\right) = 0) \land ((\operatorname{PowerSeries}.\operatorname{derivative}\left(G\right) = A) \land (\operatorname{PowerSeries}.\operatorname{subst}\left(X - G, A\right) = X + G))))$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.IsSolution` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A277403 — E.g.f. satisfies: A(x - Integral A(x) dx) = x + Integral A(x) dx.*. URL: <https://oeis.org/A277403>.

*Commentary.*

OEIS A277403, NAME and FORMULA fields, revision #21 (no page number): "E.g.f. satisfies: A(x - Integral A(x) dx) = x + Integral A(x) dx." "Let G(x) = Integral A(x) dx, then e.g.f. A(x) also satisfies:" Here A and G are rational formal series; G has zero constant coefficient and derivative A. The displayed example begins x + 2*x^2/2! + 10*x^3/3!.

**Definition 1.2 (The divisibility assertion).**

$$(claim) \Leftrightarrow (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall G \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsSolution}\left(A, G\right)) \Rightarrow ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\exists a \in \mathbb{Z},\; \operatorname{eCoeff}\left(A, n\right) = (a: \mathbb{Q}))) \land (\forall n \in \mathbb{N},\; (2 < n) \Rightarrow (\exists k \in \mathbb{Z},\; \operatorname{eCoeff}\left(A, n\right) = ((10 \cdot k: \mathbb{Z}): \mathbb{Q})))))$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A277403 — E.g.f. satisfies: A(x - Integral A(x) dx) = x + Integral A(x) dx.*. URL: <https://oeis.org/A277403>.

*Commentary.*

OEIS A277403, sole COMMENTS conjecture, revision #21 (no page number): "a(n) is divisible by 10 for n>2 (conjecture)." The offset is one. The first conjunct asserts integrality at every positive index; the second asserts divisibility at every index greater than two. Integers are explicitly cast into the rationals in both conclusions.

**Theorem 1.3 (Divisibility at every index above two).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall G \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsSolution}\left(A, G\right)) \Rightarrow ((\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\exists a \in \mathbb{Z},\; \operatorname{eCoeff}\left(A, n\right) = (a: \mathbb{Q}))) \land (\forall n \in \mathbb{N},\; (2 < n) \Rightarrow (\exists k \in \mathbb{Z},\; \operatorname{eCoeff}\left(A, n\right) = ((10 \cdot k: \mathbb{Z}): \mathbb{Q}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A277403 — E.g.f. satisfies: A(x - Integral A(x) dx) = x + Integral A(x) dx.*. URL: <https://oeis.org/A277403>.

*Commentary.*

The coefficient equation is triangular with leading coefficient one. It constructs an integral sequence and proves uniqueness over every commutative ring. Encoding that sequence produces a rational solution of the source equation, so the solution class is nonempty. For P=X+X^2 and J=X^2/2+X^3/3, the complete residual P(X-J)-X-J has exponential coefficients -10,-10,40,80 in degrees three through six and zero elsewhere. Thus P solves the coefficient equation modulo ten. Uniqueness identifies its residues with those of the integral sequence. Reduction acts on integral coefficient sequences and requires no factorial inverses modulo ten.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.IsSolution`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen.result`
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](QuarticEGFFixedPoint.md)
