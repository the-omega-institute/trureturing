# Hanna's Quadrupled Linear Rows and Dyadic Parity

## Abstract

An integer source series exists for OEIS A397594, and every source series has Hanna's dyadic-neighbor odd support.

The ordinary formal series has a(n)=PowerSeries.coeff n A, with index zero and a(0)=1. Rational rescaling substitutes X/m after mapping each integer coefficient to Q. All powers are formal-series products. Subtraction between natural indices is truncated natural subtraction; no analytic convergence is required.

**Definition 1.1 (The rational-rescaling source equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{IsSourceSeries}\left(A\right) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall m \in \mathbb{N},\; (0 < m) \Rightarrow (\sum_{j \in \operatorname{Finset}.\operatorname{range}\left(m\right)} \operatorname{PowerSeries}.\operatorname{coeff}\left(j, (\operatorname{PowerSeries}.\operatorname{rescale}\left((m: \mathbb{Q})^{-1}, \operatorname{PowerSeries}.\operatorname{map}\left(\operatorname{Int}.\operatorname{castRingHom}\left(\mathbb{Q}\right), A\right)\right))^{m}\right) = (4: \mathbb{Q})^{m - 1})))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A397594: quadrupled linear rows and dyadic parity*. URL: <https://oeis.org/A397594>.

*Commentary.*

OEIS A397594 revision 15, NAME and FORMULA (1), without pagination: "G.f. A(x) such that the sum of the first n coefficients in A(x/n)^n equals 4^(n-1) for n >= 1." "(1) 4^(n-1) = Sum_{k=0..n-1} [x^k] A(x/n)^n for n >= 1." The natural m below is the source's n, and j is its k. Finset.range m contains exactly j=0 through m-1. The equation is in Q, with A in PowerSeries Z and constant coefficient one.

**Definition 1.2 (Integer existence and the parity assertion).**

$$claim \Leftrightarrow ((\exists A \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; (\operatorname{IsSourceSeries}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; (3 < n) \Rightarrow (\operatorname{Odd}\left(\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right)\right) \Leftrightarrow (\exists k \in \mathbb{N},\; (1 < k) \land (n = 2^{k} - 1 \lor n = 2^{k} + 1))))))$$

*Formalization.* `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2026). *OEIS A397594: quadrupled linear rows and dyadic parity*. URL: <https://oeis.org/A397594>.

*Commentary.*

OEIS A397594 revision 15, COMMENTS, without pagination: "Conjecture: for n > 3, a(n) is odd iff n is of the form 2^k-1 or 2^k+1 (k > 1)." Here a(n)=PowerSeries.coeff n A, n and k are natural numbers, and Odd applies to an integer coefficient. Existence of an integer source series is included, and the equivalence quantifies over every source series.

**Theorem 1.3 (Hanna's parity assertion proved).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; (\operatorname{IsSourceSeries}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; (3 < n) \Rightarrow (\operatorname{Odd}\left(\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right)\right) \Leftrightarrow (\exists k \in \mathbb{N},\; (1 < k) \land (n = 2^{k} - 1 \lor n = 2^{k} + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A397594: quadrupled linear rows and dyadic parity*. URL: <https://oeis.org/A397594>.

*Commentary.*

Clearing the rescaling denominators gives the integer row equation. Triangular normalization has forcing 4^n(n+1)^(n-1) in positive degree. Coefficientwise iteration constructs an integer solution. The forcing vanishes modulo two, so normalized uniqueness and the homogeneous dyadic-support theorem give the parity equivalence for every source solution. The assertion concerns the parameter four; the entire parameter triangle and the source's reversion identities are separate questions.

## References

- Truth anchor: `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.claim`
- Truth anchor: `D5/S1/Recurrence/LinearRows/QuadrupledLinearExponentDyadicSupport.result`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport](LinearExponentDyadicSupport.md)
