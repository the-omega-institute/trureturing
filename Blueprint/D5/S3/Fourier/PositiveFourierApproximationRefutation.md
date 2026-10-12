# Refutation of Herrera's function-approximation conjecture

## Abstract

A positive-Fourier defect dilation and a three-point certificate refute Herrera's operator-monotone function-approximation conjecture.

**Definition 1.1 (Admissible positive-Fourier approximants).**

$$\forall g \in \mathbb{R} \to \mathbb{R},\; IsAdmissible\left(g\right) \Leftrightarrow (ContDiff\left(\mathbb{R}, 1, g\right))\land (\exists mu \in Measure\left(\mathbb{R}\right),\; (IsFiniteMeasure\left(mu\right))\land (\forall x \in \mathbb{R},\; (deriv\left(g, x\right):\mathbb{C}) = integral\left(\lambda (t: \mathbb{R}) \mapsto Complex.exp\left(-(t:\mathbb{C}) \cdot (x:\mathbb{C}) \cdot Complex.I\right), mu\right)))$$

*Formalization.* `D5/S3/Fourier/PositiveFourierApproximationRefutation.IsAdmissible` (`✓ std3`).

*Citation.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The admissible class is the source's C1 functions whose derivative is the Fourier transform of a finite positive Borel measure; the integral uses the stated complex exponential convention.

**Definition 1.2 (Approximation cost).**

$$\forall f \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall c \in \mathbb{R},\; approxCost\left(f, g, c\right) = iSup\left(\lambda (x: Set.Ici\left((0:\mathbb{R})\right)) \mapsto f\left(val\left(x\right)\right) - g\left(val\left(x\right)\right)\right) - iInf\left(\lambda (x: Set.Ici\left((0:\mathbb{R})\right)) \mapsto f\left(val\left(x\right)\right) - g\left(val\left(x\right)\right)\right) + c \cdot deriv\left(g, 0\right)$$

*Formalization.* `D5/S3/Fourier/PositiveFourierApproximationRefutation.approxCost` (`✓ std3`).

*Citation.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The cost is the oscillation of f-g on the nonnegative half-line plus c times the derivative at zero.

**Definition 1.3 (Function-approximation functional).**

$$\forall f \in \mathbb{R} \to \mathbb{R},\; \forall c \in \mathbb{R},\; approxError\left(f, c\right) = sInf\left(\{J: \mathbb{R} | \exists g \in \mathbb{R} \to \mathbb{R},\; (IsAdmissible\left(g\right))\land ((BddAbove\left(Set.range\left(\lambda (x: Set.Ici\left((0:\mathbb{R})\right)) \mapsto f\left(val\left(x\right)\right) - g\left(val\left(x\right)\right)\right)\right))\land ((BddBelow\left(Set.range\left(\lambda (x: Set.Ici\left((0:\mathbb{R})\right)) \mapsto f\left(val\left(x\right)\right) - g\left(val\left(x\right)\right)\right)\right))\land (J = approxCost\left(f, g, c\right))))\}\right)$$

*Formalization.* `D5/S3/Fourier/PositiveFourierApproximationRefutation.approxError` (`✓ std3`).

*Citation.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The infimum ranges over admissible g for which the approximation error has bounded upper and lower ranges.

**Definition 1.4 (Operator monotonicity on positive semidefinite matrices).**

$$\forall f \in \mathbb{R} \to \mathbb{R},\; OperatorMonotoneOn\left(f\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall A \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right),\; \forall B \in Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right),\; Matrix.PosSemidef\left(A\right) \Rightarrow \left(Matrix.PosSemidef\left(B\right) \Rightarrow \left(LE.le\left(A, B\right) \Rightarrow LE.le\left(cfc\left(f, A\right), cfc\left(f, B\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/PositiveFourierApproximationRefutation.OperatorMonotoneOn` (`✓ std3`).

*Citation.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The matrix order condition is imposed at every finite dimension for positive semidefinite A and B.

**Definition 1.5 (Herrera's Conjecture 2).**

$$claim \Leftrightarrow \left(\forall f \in \mathbb{R} \to \mathbb{R},\; \left(\forall x \in \mathbb{R},\; LE.le\left(0, x\right) \Rightarrow LE.le\left(0, f\left(x\right)\right)\right) \Rightarrow \left(OperatorMonotoneOn\left(f\right) \Rightarrow \left(\forall c \in \mathbb{R},\; LT.lt\left(0, c\right) \Rightarrow LE.le\left(approxError\left(f, c\right), f\left(c\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Fourier/PositiveFourierApproximationRefutation.claim` (`✓ std3`).

*Citation.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The source sentence is verbatim (arXiv v1, p. 7): “Let f be a non-negative function that is operator monotone on [0, ∞). Then E_f(c) ≤ Cf(c) holds for all c > 0 when C = 1.” This is Conjecture 2, numbered 1.10 in print; the formula binds the Lean encoding of f, operator monotonicity, c and positivity.

**Theorem 1.6 (The conjecture is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/PositiveFourierApproximationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/herrera-2023-function-approximation-conjecture` (refuted) by `D5/S3/Fourier/PositiveFourierApproximationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"herrera-2023-function-approximation-conjecture","declaration_gid":"D5/S3/Fourier/PositiveFourierApproximationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Herrera (2023). *On the commutator modulus of continuity for operator monotone functions*. URL: <https://arxiv.org/abs/2311.17448v1>.

*Commentary.*

The witness is f(x)=x/(1+x) at c=1. Positive Fourier structure gives a cubic defect-dilation bound, and the three-point comparison forces every admissible approximant to have cost at least 1153/2304, while f(1)=1/2. The function is nonnegative and operator monotone by the resolvent formula.

The source's bound C<1.01975 remains an upper bound for this function. The optimal constant is open between 1153/1152 and 1.01975; the paper's commutator Conjectures 1 and 3 remain open because the implication from Conjecture 2 is not reversible.

## References

- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.IsAdmissible`
- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.OperatorMonotoneOn`
- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.approxCost`
- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.approxError`
- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.claim`
- Truth anchor: `D5/S3/Fourier/PositiveFourierApproximationRefutation.result`
