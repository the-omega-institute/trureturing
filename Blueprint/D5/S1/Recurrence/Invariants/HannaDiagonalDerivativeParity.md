# Hanna's A375449 Diagonal Derivative Parity

## Abstract

The diagonal derivative equation has integral coefficients, with odd coefficients at exactly two Mersenne supports above degree one.

PowerSeries denotes formal power series over the rational numbers. The symbol X is the indeterminate, derivative is the formal derivative, coeff extracts a coefficient, and C embeds a scalar as a constant series. The inverse is taken in the formal power-series ring; the denominator has constant coefficient one. Indices and powers are natural numbers, and subtraction in the support indices is natural subtraction. The displayed rational coercion identifies each coefficient with an integer m.

**Definition 1.1 (The diagonal coefficient recursion).**

$$\forall R: Type*, [\operatorname{CommRing}\left(R\right)], \forall t: \mathbb{N} \to R, \forall f: \operatorname{PowerSeries}\left(R\right), \operatorname{step}\left(t, f\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{ite}\left(n = 0, 0, t\left(n\right) - \operatorname{coeff}\left(n, X \cdot \operatorname{derivative}\left(f\right) \cdot f \cdot \operatorname{invOfUnit}\left(1 - \operatorname{C}\left((n: R)\right) \cdot f, 1\right)\right)\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a commutative ring R, a forcing sequence t and a series f, the constant coefficient is zero. At every positive index n, subtract coefficient n of the displayed nonlinear series from t(n). At f=0 this retains exactly the positive coefficients of t.

**Definition 1.2 (An arbitrary diagonal forcing sequence).**

$$\forall t: (\mathbb{N} \to \mathbb{Q}), \forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsDiagonal}\left(t, A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, X \cdot \operatorname{derivative}\left(A\right) \cdot (1 - \operatorname{C}\left((n: \mathbb{Q})\right) \cdot A)^{-1}\right) = (n: \mathbb{Q}) \cdot t\left(n\right))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.IsDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The diagonal derivative coefficient at positive index n equals n times the rational forcing value t(n). The constant coefficient of the solution is zero.

**Theorem 1.3 (Integral existence and universal parity).**

$$\forall t: (\mathbb{N} \to \mathbb{Z}), (\forall n: \mathbb{N}, (1 \le n) \implies ((t\left(n\right): \operatorname{ZMod}\left(2\right)) = (n: \operatorname{ZMod}\left(2\right)))) \implies ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsDiagonal}\left((n: \mathbb{N} \mapsto (t\left(n\right): \mathbb{Q})), A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsDiagonal}\left((n: \mathbb{N} \mapsto (t\left(n\right): \mathbb{Q})), A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, (1 < k) \land ((n = (2)^{k} - 2) \lor (n = (2)^{k} - 1))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.diagonal_integral_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

Rewrite the diagonal equation as a(n)=t(n) minus coefficient n of X*A'(X)*A(X)/(1-n*A(X)). This nonlinear expression gains one degree of coefficient agreement. Translating by one applies PowerSeriesNormalizedContraction.exists_unique_fixed. The fixed point is integral, and uniqueness is preserved by extension to the rational numbers. When the forcing sequence reduces to n modulo two, the solution reduces to T+T squared, where T is the reduction of UnitReversionSquareParity.generatingSeries. That series satisfies T=X+X*T squared. Euler differentiation separates its odd support from the even support of its square. For Q=T/(1+T+T squared), clearing unit denominators gives Q+Q squared=X/(1+X squared). Consequently every odd coefficient of Q is one. The Mersenne support theorem for T then gives the two support families. Taking t(n)=n^n or n^(n-1) proves the A375449 and A375452 assertions.

**Definition 1.4 (The normalized generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, X \cdot \operatorname{derivative}\left(A\right) \cdot (1 - \operatorname{C}\left((n: \mathbb{Q})\right) \cdot A)^{-1}\right) = ((n: \mathbb{Q}))^{n + 1})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The Name field of the unpaginated OEIS A375449 entry states: "Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^(n+1) for n >= 1." The offset is one, encoded by zero constant coefficient. The scalar n in C is a rational number.

**Definition 1.5 (The coefficient parity proposition).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, (1 < k) \land ((n = (2)^{k} - 2) \lor (n = (2)^{k} - 1))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The Comments field of the unpaginated OEIS A375449 entry states: "Conjecture: for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1 for some k > 1." Here a(n) is coefficient n of any normalized rational solution. The proposition also states existence and integrality of the indicated coefficients.

**Theorem 1.6 (The A375449 parity theorem).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, (1 < k) \land ((n = (2)^{k} - 2) \lor (n = (2)^{k} - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a375449-hanna-diagonal-parity` (proved) by `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a375449-hanna-diagonal-parity","declaration_gid":"D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The integer forcing sequence is n to the power n. For every positive n its residue modulo two equals that of n. The shared diagonal recursion constructs an integral solution. Over ZMod(2), its reduction is the sum of the Mersenne series T and T squared. The two summands have odd and even support respectively, which gives the equivalence.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.IsDiagonal`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.diagonal_integral_parity`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity.step`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Residue/ContinuedFractionOddSquare](../Residue/ContinuedFractionOddSquare.md)
