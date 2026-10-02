# Zeitlin Six-J Expansion

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Theorem 1.1 (racah expansion open).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (2 \le N) \Rightarrow ((i < N) \Rightarrow ((j < N) \Rightarrow ((((\mathrm{asReal}\left(-1\right))^{(((N) - (1)) + (i)) + (j)}) \cdot (\mathrm{real}\left(N\right))) \cdot (\mathrm{Wij}\left(N, i, j\right)) = \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{racahPolynomial}\left(N, j, i\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.racah_expansion_open` (`✓ std3`). ∎

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The normalized Wigner symbol equals the terminating Racah polynomial. The recurrence and zero-row initial value identify the two sequences over the full finite range.

**Definition 1.2 (rawAlpha).**

$$\forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{rawAlpha}\left(a, b, c, d, y\right)\right) = \mathrm{div}\left(((((y) + (1))^{2}) - (((a) - (d))^{2})) \cdot ((((y) + (1))^{2}) - (((b) - (c))^{2})), ((2) \cdot ((y) + (1))) \cdot (((2) \cdot (y)) + (1))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of rawAlpha.

**Definition 1.3 (rawGamma).**

$$\forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{rawGamma}\left(a, b, c, d, y\right)\right) = \mathrm{div}\left((((((a) + (d)) + (1))^{2}) - ((y)^{2})) \cdot (((((b) + (c)) + (1))^{2}) - ((y)^{2})), ((2) \cdot (y)) \cdot (((2) \cdot (y)) + (1))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of rawGamma.

**Definition 1.4 (rawDiagonal).**

$$\forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{rawDiagonal}\left(a, b, c, d, y\right)\right) = (((a) \cdot ((a) + (1))) + ((b) \cdot ((b) + (1)))) - (\mathrm{div}\left(((((y) \cdot ((y) + (1))) + ((a) \cdot ((a) + (1)))) - ((d) \cdot ((d) + (1)))) \cdot ((((y) \cdot ((y) + (1))) + ((b) \cdot ((b) + (1)))) - ((c) \cdot ((c) + (1)))), ((2) \cdot (y)) \cdot ((y) + (1))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of rawDiagonal.

**Definition 1.5 (fourSpinDenominator).**

$$\forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{fourSpinDenominator}\left(y\right)\right) = (((2) \cdot (y)) \cdot ((y) + (1))) \cdot (((2) \cdot (y)) + (1))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of fourSpinDenominator.

**Definition 1.6 (fourSpinCertificateNumerator).**

$$\forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall u \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \forall z \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{fourSpinCertificateNumerator}\left(a, b, c, d, u, y, z\right)\right) = ((((((-\left((y) + (1)\right)) \cdot ((((b) + (c)) + (1)) - (y))) \cdot ((((a) + (d)) + (y)) + (1))) \cdot ((((a) - (b)) + (u)) + (1))) \cdot ((((d) - (c)) + (u)) + (1))) + ((((2) \cdot ((y) + (1))) \cdot ((((u) + (1)) \cdot (((((a) + (d)) + (1)) \cdot (((b) + (c)) + (1))) - ((y)^{2}))) + ((y) \cdot ((((a) - (b)) \cdot ((c) - (d))) - (((u) + (1))^{2}))))) \cdot ((z) - (((b) + (c)) + (y))))) + (((((((((2) \cdot (u)) \cdot (y)) \cdot ((y) + (1))) + ((y)^{2})) - ((((a) + (d)) + (1)) \cdot (((b) + (c)) + (1)))) - ((y) \cdot ((((((((2) \cdot (a)) \cdot (c)) + (((2) \cdot (b)) \cdot (d))) + (a)) + (b)) + (c)) + (d)))) \cdot ((z) - (((b) + (c)) + (y)))) \cdot ((z) - (((a) + (d)) + (y))))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinCertificateNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of fourSpinCertificateNumerator.

**Definition 1.7 (fourSpinCertificate).**

$$\forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall u \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \forall z \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{fourSpinCertificate}\left(a, b, c, d, u, y, z\right)\right) = \mathrm{div}\left(\mathrm{fourSpinCertificateNumerator}\left(a, b, c, d, u, y, z\right), \mathrm{fourSpinDenominator}\left(y\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of fourSpinCertificate.

**Definition 1.8 (compressedAlpha).**

$$\forall h \in \mathit{Rat},\; \forall v \in \mathit{Rat},\; \forall p \in \mathit{Rat},\; \forall q \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedAlpha}\left(h, v, p, q, y\right)\right) = (y) \cdot (((((p) - (q))^{2}) - ((((2) \cdot ((y) + (1))) \cdot (((v) - ((2) \cdot (y))) - (2))) \cdot ((p) - (q)))) + (((4) \cdot (((y) + (1))^{2})) \cdot (q)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedAlpha.

**Definition 1.9 (compressedBeta).**

$$\forall m \in \mathit{Rat},\; \forall h \in \mathit{Rat},\; \forall v \in \mathit{Rat},\; \forall p \in \mathit{Rat},\; \forall q \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedBeta}\left(m, h, v, p, q, y\right)\right) = (-\left(((2) \cdot (y)) + (1)\right)) \cdot (((((p) - (q)) \cdot (((m) + ((y) \cdot (h))) - (y))) + ((((2) \cdot (y)) \cdot ((y) + (1))) \cdot (p))) + ((((y) + (1)) \cdot ((m) + (((2) \cdot (y)) \cdot (h)))) \cdot ((1) - (v))))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedBeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedBeta.

**Definition 1.10 (compressedGamma).**

$$\forall m \in \mathit{Rat},\; \forall h \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedGamma}\left(m, h, y\right)\right) = (((y) + (1)) \cdot (m)) \cdot ((m) + (((2) \cdot (y)) \cdot (h)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedGamma.

**Definition 1.11 (compressedV).**

$$\forall v \in \mathit{Rat},\; \forall p \in \mathit{Rat},\; \forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedV}\left(v, p, x\right)\right) = (((x)^{2}) - ((v) \cdot (x))) + (p)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedV.

**Definition 1.12 (compressedZ).**

$$\forall m \in \mathit{Rat},\; \forall h \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedZ}\left(m, h, y, x\right)\right) = (((m) + ((((2) \cdot (y)) + (1)) \cdot ((h) - (1)))) + ((((h) - ((2) \cdot (y))) - (2)) \cdot (x))) - ((x)^{2})$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedZ.

**Definition 1.13 (compressedQ).**

$$\forall v \in \mathit{Rat},\; \forall q \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedQ}\left(v, q, y, x\right)\right) = (((x)^{2}) - ((((v) - ((2) \cdot (y))) - (2)) \cdot (x))) + (q)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedQ.

**Definition 1.14 (compressedCertificate).**

$$\forall m \in \mathit{Rat},\; \forall h \in \mathit{Rat},\; \forall v \in \mathit{Rat},\; \forall p \in \mathit{Rat},\; \forall q \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; \forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{compressedCertificate}\left(m, h, v, p, q, y, x\right)\right) = ((((-\left((y) + (1)\right)) \cdot (m)) \cdot (p)) + ((((y) + (1)) \cdot ((((v) - (h)) \cdot ((m) + (((2) \cdot (y)) \cdot (h)))) - (((2) \cdot (y)) \cdot (p)))) \cdot (x))) + ((((((y) \cdot ((p) - (q))) - (((y) + (1)) \cdot (m))) - ((((2) \cdot (y)) \cdot ((y) + (1))) \cdot (h))) \cdot (x)) \cdot ((x) - (h)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of compressedCertificate.

**Definition 1.15 (RacahOffsets).**

$$\mathrm{Structure}\left(\mathit{RacahOffsets}, \mathrm{Fields}\left(\mathit{ta}, \mathit{tb}, \mathit{tc}, \mathit{td}, e, f, g\right), \mathit{Int}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.RacahOffsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of RacahOffsets.

**Definition 1.16 (Offsets raise).**

$$\forall q \in \mathit{RacahOffsets},\; (\mathrm{raise}\left(q\right):\mathit{RacahOffsets}) = \mathrm{mk}\left((\mathrm{ta}\left(q\right)) + (1), (\mathrm{tb}\left(q\right)) + (1), \mathrm{tc}\left(q\right), \mathrm{td}\left(q\right), \mathrm{e}\left(q\right), (\mathrm{f}\left(q\right)) + (1), (\mathrm{g}\left(q\right)) + (1)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.raise` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of RacahOffsets.raise.

**Definition 1.17 (Offsets lower).**

$$\forall q \in \mathit{RacahOffsets},\; (\mathrm{lower}\left(q\right):\mathit{RacahOffsets}) = \mathrm{mk}\left((\mathrm{ta}\left(q\right)) - (1), (\mathrm{tb}\left(q\right)) - (1), \mathrm{tc}\left(q\right), \mathrm{td}\left(q\right), \mathrm{e}\left(q\right), (\mathrm{f}\left(q\right)) - (1), (\mathrm{g}\left(q\right)) - (1)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of RacahOffsets.lower.

**Definition 1.18 (offsetTerm).**

$$\forall q \in \mathit{RacahOffsets},\; \forall z \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{offsetTerm}\left(q, z\right)\right) = (((((((((\mathrm{asRat}\left(-1\right))^{z}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) + (1)\right)\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{ta}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tb}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tc}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{td}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{e}\left(q\right)) - (\mathrm{int}\left(z\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{f}\left(q\right)) - (\mathrm{int}\left(z\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{g}\left(q\right)) - (\mathrm{int}\left(z\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of offsetTerm.

**Definition 1.19 (offsetBase).**

$$\forall q \in \mathit{RacahOffsets},\; \forall z \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{offsetBase}\left(q, z\right)\right) = (((((((((\mathrm{asRat}\left(-1\right))^{z}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) + (1)\right)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{ta}\left(q\right))) + (1)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tb}\left(q\right))) + (1)\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tc}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{td}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{e}\left(q\right)) - (\mathrm{int}\left(z\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{f}\left(q\right)) - (\mathrm{int}\left(z\right))) + (1)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{g}\left(q\right)) - (\mathrm{int}\left(z\right))) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of offsetBase.

**Definition 1.20 (offsetFlux).**

$$\forall q \in \mathit{RacahOffsets},\; \forall P \in \mathit{Rat} \to \mathit{Rat},\; \forall z \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{offsetFlux}\left(q, P, z\right)\right) = ((((((((((\mathrm{asRat}\left(-1\right))^{z}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) + (1)\right)\right))) \cdot (P\left(\mathrm{asRat}\left(\mathrm{rat}\left(z\right)\right)\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{ta}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tb}\left(q\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{tc}\left(q\right))) - (1)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(z\right)\right)) - (\mathrm{td}\left(q\right))) - (1)\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{e}\left(q\right)) - (\mathrm{int}\left(z\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{f}\left(q\right)) - (\mathrm{int}\left(z\right))) + (1)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{g}\left(q\right)) - (\mathrm{int}\left(z\right))) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetFlux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of offsetFlux.

**Definition 1.21 (Offsets compatible).**

$$\forall q \in \mathit{RacahOffsets},\; \forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall u \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; (\mathrm{compatible}\left(q, a, b, c, d, u, y\right):\mathit{Prop}) = \left((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{ta}\left(q\right)\right)\right) = ((a) + (d)) + (y)) \land ((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{tb}\left(q\right)\right)\right) = ((b) + (c)) + (y)) \land ((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{tc}\left(q\right)\right)\right) = ((a) + (b)) + (u)) \land ((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{td}\left(q\right)\right)\right) = ((c) + (d)) + (u)) \land ((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{e}\left(q\right)\right)\right) = (((a) + (b)) + (c)) + (d)) \land ((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{f}\left(q\right)\right)\right) = (((a) + (c)) + (u)) + (y)) \land (\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{g}\left(q\right)\right)\right) = (((b) + (d)) + (u)) + (y)))))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of RacahOffsets.compatible.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.RacahOffsets`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compatible`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedAlpha`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedBeta`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedCertificate`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedGamma`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedQ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedV`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.compressedZ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinCertificate`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinCertificateNumerator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.fourSpinDenominator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.lower`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetBase`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetFlux`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.offsetTerm`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.racah_expansion_open`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.raise`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawAlpha`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawDiagonal`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion.rawGamma`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah](Racah.md)
