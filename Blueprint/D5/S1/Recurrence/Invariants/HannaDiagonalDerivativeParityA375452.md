# Hanna's A375452 Diagonal Derivative Parity

## Abstract

The diagonal derivative equation has integral coefficients, with odd coefficients at exactly two Mersenne supports above degree one.

PowerSeries denotes formal power series over the rational numbers. The symbol X is the indeterminate, derivative is the formal derivative, coeff extracts a coefficient, and C embeds a scalar as a constant series. The inverse is taken in the formal power-series ring; the denominator has constant coefficient one. Indices and powers are natural numbers, and subtraction in the support indices is natural subtraction. The displayed rational coercion identifies each coefficient with an integer m.

**Definition 1.1 (The normalized generating equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, X \cdot \operatorname{derivative}\left(A\right) \cdot (1 - \operatorname{C}\left((n: \mathbb{Q})\right) \cdot A)^{-1}\right) = ((n: \mathbb{Q}))^{n})))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The Name field of the unpaginated OEIS A375452 entry states: "Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^n for n >= 1." The offset is one, encoded by zero constant coefficient. The scalar n in C is a rational number.

**Definition 1.2 (The coefficient parity proposition).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, (1 < k) \land ((n = (2)^{k} - 2) \lor (n = (2)^{k} - 1))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The Comments field of the unpaginated OEIS A375452 entry states: "Conjecture: for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1 for some k > 1." Here a(n) is coefficient n of any normalized rational solution. The proposition also states existence and integrality of the indicated coefficients.

**Theorem 1.3 (The A375452 parity theorem).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists m: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land ((\operatorname{Odd}\left(m\right)) \iff (\exists k: \mathbb{N}, (1 < k) \land ((n = (2)^{k} - 2) \lor (n = (2)^{k} - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a375452-hanna-diagonal-parity` (proved) by `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a375452-hanna-diagonal-parity","declaration_gid":"D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A375449 and A375452, diagonal derivative parity conjectures*. URL: <https://oeis.org/A375449>.

*Commentary.*

The integer forcing sequence is n^(n-1). For every positive n its residue modulo two equals that of n. The shared diagonal recursion constructs an integral solution. Over ZMod(2), its reduction is the sum of the Mersenne series T and T squared. The two summands have odd and even support respectively, which gives the equivalence.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452.result`
- Dependency: [D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity](HannaDiagonalDerivativeParity.md)
