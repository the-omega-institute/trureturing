# Quet's Rational Iteration Denominator Recurrence

## Abstract

The reduced denominators of Quet's rational iteration satisfy his recurrence.

**Definition 1.1 (Pair-recurrence numerator).**

$$\begin{aligned}num \in \left(\mathrm{Nat} \to \mathrm{Nat}\right)\\num\left(0\right) = 0\\num\left(1\right) = 1\\\forall n \in \mathrm{Nat},\; num\left(n + 2\right) = num\left(n + 1\right) \cdot (num\left(n + 1\right) + 2 \cdot den\left(n + 1\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.num` (`✓ std3`).

*Citation.* Leroy Quet; N. J. A. Sloane (2003). *OEIS A079278, denominators of the rational iteration b(n) = b(n-1) + 1/(1 + 1/b(n-1))*. URL: <https://oeis.org/A079278>.

*Commentary.*

The auxiliary numerator starts with num(0)=0 and num(1)=1. Each later value is the preceding numerator multiplied by that numerator plus twice the preceding denominator.

**Definition 1.2 (Pair-recurrence denominator).**

$$\begin{aligned}den \in \left(\mathrm{Nat} \to \mathrm{Nat}\right)\\den\left(0\right) = 1\\den\left(1\right) = 1\\\forall n \in \mathrm{Nat},\; den\left(n + 2\right) = den\left(n + 1\right) \cdot (num\left(n + 1\right) + den\left(n + 1\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.den` (`✓ std3`).

*Citation.* Leroy Quet; N. J. A. Sloane (2003). *OEIS A079278, denominators of the rational iteration b(n) = b(n-1) + 1/(1 + 1/b(n-1))*. URL: <https://oeis.org/A079278>.

*Commentary.*

The denominator starts with den(0)=den(1)=1. Each later value is the preceding denominator multiplied by the sum of the preceding numerator and denominator.

**Definition 1.3 (Quet's rational iteration).**

$$\begin{aligned}b \in \left(\mathrm{Nat} \to \mathrm{Rat}\right)\\b\left(0\right) = 0\\b\left(1\right) = 1\\\forall n \in \mathrm{Nat},\; b\left(n + 2\right) = b\left(n + 1\right) + 1 / (1 + 1 / b\left(n + 1\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.b` (`✓ std3`).

*Citation.* Leroy Quet; N. J. A. Sloane (2003). *OEIS A079278, denominators of the rational iteration b(n) = b(n-1) + 1/(1 + 1/b(n-1))*. URL: <https://oeis.org/A079278>.

*Commentary.*

The rational sequence is extended by b(0)=0 and begins with b(1)=1. At every later index it adds one divided by one plus the reciprocal of the preceding value.

**Theorem 1.4 (Quet's denominator recurrence).**

$$\forall m \in \mathrm{Nat},\; (2 \le m) \Rightarrow ((den\left(m - 1\right)^{2} \mid den\left(m\right)^{3}) \land (den\left(m + 1\right) = den\left(m\right)^{2} + den\left(m\right)^{3} / den\left(m - 1\right)^{2} - den\left(m\right) \cdot den\left(m - 1\right)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a079278-quet-rational-iteration-denominator-recurrence` (proved) by `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a079278-quet-rational-iteration-denominator-recurrence","declaration_gid":"D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Leroy Quet; N. J. A. Sloane (2003). *OEIS A079278, denominators of the rational iteration b(n) = b(n-1) + 1/(1 + 1/b(n-1))*. URL: <https://oeis.org/A079278>.

*Commentary.*

For every m at least two, the square of den(m-1) divides the cube of den(m), and den(m+1) satisfies Quet's formula. The divisibility clause makes the natural-number quotient exact. Writing a reduced rational as p/q turns the iteration into the pair step (p,q) to (p(p+2q),q(p+q)); coprimality is preserved, and the numerator recurrence yields the equation.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.b`
- Truth anchor: `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.den`
- Truth anchor: `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.num`
- Truth anchor: `D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.result`
