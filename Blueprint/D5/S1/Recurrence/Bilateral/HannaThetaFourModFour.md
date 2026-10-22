# Hanna's theta-four congruences

## Abstract

Hanna's A379764 theta-four coefficient conjectures.

Paul D. Hanna's OEIS A379764 states: "G.f. A(x) satisfies Sum_{n=-oo..+oo} (4^n*A(x)^n - 4*A(x))^(n+1) = 2*theta_4(x) = 2*Sum_{n=-oo..+oo} (-x)^(n^2)." The same entry states: "Conjecture: for n > 0, a(n) is odd iff n is a square." It also states: "Conjecture: for n > 0, a(n) == (-1)^(n-1) (mod 4) iff n is a square, otherwise a(n) is divisible by 4 if n is nonsquare."

PowerSeries and LaurentSeries are formal series over the displayed coefficient rings. The bilateral sum is coefficientwise over the finite interval Icc(-(K:Z), K) with N+1 <= K. The coefficient of theta4 is defined by the same finite symmetric window. Int.ModEq is congruence modulo its first argument; divisibility is in Z.

**Definition 1.1 (The coefficientwise theta-four series).**

$$\operatorname{theta4}\left(\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((N: \mathbb{N} \mapsto \sum_{n: \mathbb{Z} \in \operatorname{Finset}.\operatorname{Icc}\left(-((N: \mathbb{Z})), (N: \mathbb{Z})\right)} ((\operatorname{if} ((n)^{2} = (N: \mathbb{Z})) \operatorname{then} (-(1))^{N} \operatorname{else} 0)))\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.theta4` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A379764, theta-four bilateral generating function and coefficient congruences*. URL: <https://oeis.org/A379764>.

*Commentary.*

The coefficient at N sums the terms indexed by integer n in the symmetric interval from -(N:Z) to N.

**Definition 1.2 (The Laurent-series summand).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall n \in \mathbb{Z},\; \operatorname{term}\left(A, n\right) = ((4)^{n} \cdot (\operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, A\right))^{n} - 4 \cdot \operatorname{HahnSeries}.\operatorname{ofPowerSeries}\left(\mathbb{Z}, \mathbb{Q}, A\right))^{n + 1}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.term` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A379764, theta-four bilateral generating function and coefficient congruences*. URL: <https://oeis.org/A379764>.

*Commentary.*

The integer exponent n is used in LaurentSeries Q after embedding A with HahnSeries.ofPowerSeries.

**Definition 1.3 (The normalized generating-function equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Leftrightarrow ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\forall N \in \mathbb{N},\; \forall K \in \mathbb{N},\; (N + 1 \le K) \Rightarrow (\sum_{j: \mathbb{Z} \in \operatorname{Finset}.\operatorname{Icc}\left(-((K: \mathbb{Z})), (K: \mathbb{Z})\right)} (\operatorname{coeff}\left((N: \mathbb{Z}), \operatorname{term}\left(A, j\right)\right)) = 2 \cdot \operatorname{coeff}\left(N, \operatorname{theta4}\left(\right)\right)))))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A379764, theta-four bilateral generating function and coefficient congruences*. URL: <https://oeis.org/A379764>.

*Commentary.*

Normalization is constantCoeff A = 0 and coeff 1 A = 1; every coefficient window with N+1 <= K equals twice the theta-four coefficient.

**Definition 1.4 (Hanna's two coefficient conjectures).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\exists m \in \mathbb{Z},\; (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (((\operatorname{Odd}\left(m\right)) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land (((\operatorname{Int}.\operatorname{ModEq}\left(4, m, (-(1))^{n - 1}\right)) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land ((\neg (\operatorname{IsSquare}\left(n\right))) \Rightarrow (4 \mid m)))))))$$

*Formalization.* `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A379764, theta-four bilateral generating function and coefficient congruences*. URL: <https://oeis.org/A379764>.

*Commentary.*

For every normalized solution and every positive n, an integer coefficient witness has the two square biconditionals and the nonsquare divisibility conclusion.

**Theorem 1.5 (The two A379764 conjectures).**

$$(\exists A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsGF}\left(A\right)) \land (\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; (\operatorname{IsGF}\left(A\right)) \Rightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\exists m \in \mathbb{Z},\; (\operatorname{coeff}\left(n, A\right) = (m: \mathbb{Q})) \land (((\operatorname{Odd}\left(m\right)) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land (((\operatorname{Int}.\operatorname{ModEq}\left(4, m, (-(1))^{n - 1}\right)) \Leftrightarrow (\operatorname{IsSquare}\left(n\right))) \land ((\neg (\operatorname{IsSquare}\left(n\right))) \Rightarrow (4 \mid m)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A379764, theta-four bilateral generating function and coefficient congruences*. URL: <https://oeis.org/A379764>.

*Commentary.*

The integral fixed-point construction gives a normalized solution. Its coefficient congruence is the theta-four source modulo four, and uniqueness identifies every normalized rational solution with it.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.IsGF`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.claim`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.result`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.term`
- Truth anchor: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.theta4`
- Dependency: [D5/S1/Recurrence/Bilateral/BilateralProductModFour](BilateralProductModFour.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S1/Recurrence/Invariants/UnitReversionSquareParity](../Invariants/UnitReversionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour](../Parity/BilateralQuarticPowerThetaModFour.md)
- Dependency: [D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen](../Parity/ScaledQuadraticReversionModSixteen.md)
