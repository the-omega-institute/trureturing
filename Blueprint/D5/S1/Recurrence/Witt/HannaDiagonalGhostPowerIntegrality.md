# Hanna's Diagonal Ghost-Power Integrality

## Abstract

Diagonal self-powers preserve integrality of formal exponential ghost series.

All series are ordinary formal power series. K is an arbitrary characteristic-zero field, and the integer image is its canonical one. The zeroth sequence entry is ignored. The logarithmic input has constant coefficient zero, so formal exponential substitution is defined. Division in the displayed logarithmic input is division in K. No positivity, nonzero-ghost or convergence hypothesis occurs.

**Definition 1.1 (The positive-degree logarithmic input).**

$$\forall K: Type*, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall C: \mathbb{N} \to K, \operatorname{logarithmicInput}\left(C\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((fun n: \mathbb{N} \mapsto \operatorname{ite}\left(n = 0, 0, \frac{C\left(n\right)}{(n: K)}\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.logarithmicInput` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *OEIS A156216: diagonal ghost-power integrality conjecture*. URL: <https://oeis.org/A156216/internal>.

*Commentary.*

OEIS A156216, internal revision #3, second comment (unpaginated): "More generally, if exp( Sum_{n>=1} C(n) * x^n/n ) equals a power series in x with integer coefficients, then exp( Sum_{n>=1} C(n)^n * x^n/n ) also equals a power series in x with integer coefficients (conjecture)." The expression Sum_{n>=1} C(n) * x^n/n is encoded coefficientwise by PowerSeries.mk, with degree zero set to zero and coefficient C(n)/(n:K) at every positive degree.

**Definition 1.2 (The literal formal exponential).**

$$\forall K: Type*, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall C: \mathbb{N} \to K, \operatorname{exponentialSum}\left(C\right) = \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{logarithmicInput}\left(C\right), \operatorname{PowerSeries}.\operatorname{exp}\left(K\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponentialSum` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *OEIS A156216: diagonal ghost-power integrality conjecture*. URL: <https://oeis.org/A156216/internal>.

*Commentary.*

OEIS A156216, internal revision #3, second comment (unpaginated): "More generally, if exp( Sum_{n>=1} C(n) * x^n/n ) equals a power series in x with integer coefficients, then exp( Sum_{n>=1} C(n)^n * x^n/n ) also equals a power series in x with integer coefficients (conjecture)." The exponential is PowerSeries.exp over K, substituted at the positive-degree logarithmic input.

**Definition 1.3 (Hanna's second-comment conjecture).**

$$claim = (\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall C: \mathbb{N} \to K, \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{exponentialSum}\left(C\right)\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{exponentialSum}\left((fun n: \mathbb{N} \mapsto C\left(n\right)^{n})\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2009). *OEIS A156216: diagonal ghost-power integrality conjecture*. URL: <https://oeis.org/A156216/internal>.

*Commentary.*

OEIS A156216, internal revision #3, second comment (unpaginated): "More generally, if exp( Sum_{n>=1} C(n) * x^n/n ) equals a power series in x with integer coefficients, then exp( Sum_{n>=1} C(n)^n * x^n/n ) also equals a power series in x with integer coefficients (conjecture)." The sequence C ranges over all natural indices, its entry at zero is unused, and C(n)^n raises the nth entry to its own natural index. IntegralSeries is the existing predicate asserting that every ordinary coefficient is an embedded integer. All fields and both field instances are quantified.

**Theorem 1.4 (Diagonal self-powers preserve integrality).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)], \forall C: \mathbb{N} \to K, \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{exponentialSum}\left(C\right)\right) \Rightarrow \operatorname{HannaLogarithmicPowerClosure}.\operatorname{IntegralSeries}\left(\operatorname{exponentialSum}\left((fun n: \mathbb{N} \mapsto C\left(n\right)^{n})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/a156216-diagonalghost` (proved) by `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"a156216-diagonalghost","declaration_gid":"D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A156216: diagonal ghost-power integrality conjecture*. URL: <https://oeis.org/A156216/internal>.

*Commentary.*

The integral input series has an integer Euler ledger b. Its formal logarithmic derivative identifies each positive ghost C(n) with the integer divisor sum of d*b(d). Nested divisor sums give local Gauss congruences. Fermat lifting together with power preservation of base congruences proves those congruences for C(n)^n, including signed and zero ghosts. Integer Moebius inversion supplies the output Euler ledger. Coefficientwise uniqueness of the differential equation X*f'=L*f with prescribed constant coefficient identifies the integer Euler series with the displayed formal exponential. Each coefficient involves only finite sums and finite Euler prefixes.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.exponentialSum`
- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.logarithmicInput`
- Truth anchor: `D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](../Algebraic/HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity](../Invariants/HannaDiagonalDerivativeParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](../LinearRows/LinearExponentDyadicSupport.md)
- Dependency: [D5/S1/Recurrence/Witt/PrimitiveEulerLedger](PrimitiveEulerLedger.md)
