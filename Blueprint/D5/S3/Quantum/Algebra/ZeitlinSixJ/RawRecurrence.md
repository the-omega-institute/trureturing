# Zeitlin Six-J RawRecurrence

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. RacahOffsetse denotes the qualified projection RacahOffsets.e. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Lemma 1.1 (four spin raw recurrence).**

$$\forall q \in \mathit{RacahOffsets},\; \forall a \in \mathit{Rat},\; \forall b \in \mathit{Rat},\; \forall c \in \mathit{Rat},\; \forall d \in \mathit{Rat},\; \forall u \in \mathit{Rat},\; \forall y \in \mathit{Rat},\; (\mathrm{compatible}\left(q, a, b, c, d, u, y\right)) \Rightarrow ((0 \le \mathrm{tc}\left(q\right)) \Rightarrow (\forall e \in \mathit{Nat},\; (\mathrm{RacahOffsetse}\left(q\right) = \mathrm{asInt}\left(\mathrm{int}\left(e\right)\right)) \Rightarrow ((y \ne 0) \Rightarrow (((y) + (1) \ne 0) \Rightarrow ((((2) \cdot (y)) + (1) \ne 0) \Rightarrow ((((\mathrm{rawAlpha}\left(a, b, c, d, y\right)) \cdot (\sum_{z\in\mathrm{range}\left((e) + (1)\right)}(\mathrm{offsetTerm}\left(\mathrm{raise}\left(q\right), z\right)))) + (((\mathrm{rawDiagonal}\left(a, b, c, d, y\right)) - ((u) \cdot ((u) + (1)))) \cdot (\sum_{z\in\mathrm{range}\left((e) + (1)\right)}(\mathrm{offsetTerm}\left(q, z\right))))) + ((\mathrm{rawGamma}\left(a, b, c, d, y\right)) \cdot (\sum_{z\in\mathrm{range}\left((e) + (1)\right)}(\mathrm{offsetTerm}\left(\mathrm{lower}\left(q\right), z\right)))) = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.four_spin_raw_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-extended factorial terms satisfy a WZ identity. Summing its exact flux with both boundary values zero gives this four-spin recurrence.

**Definition 1.2 (racahOffsets).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall u \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; (\mathrm{racahOffsets}\left(a, b, u, c, d, y\right):\mathit{RacahOffsets}) = \mathrm{mk}\left(\mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left(((a) + (d)) + (y), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left(((c) + (b)) + (y), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left(((a) + (b)) + (u), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left(((c) + (d)) + (u), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left((((a) + (b)) + (c)) + (d), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left((((u) + (a)) + (y)) + (c), 2\right)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left(\mathrm{natDiv}\left((((b) + (u)) + (d)) + (y), 2\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.racahOffsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of racahOffsets.

**Lemma 1.3 (racahSum recurrence).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall u \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; (2 \le y) \Rightarrow ((\mathrm{admissible}\left(a, b, u, c, d, y\right)) \Rightarrow ((((\mathrm{rawAlpha}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(c\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(d\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)\right)) \cdot (\mathrm{racahSum}\left(a, b, u, c, d, (y) + (2)\right))) + (((\mathrm{rawDiagonal}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(c\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(d\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)\right)) - ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(u\right)\right), 2\right)) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(u\right)\right), 2\right)) + (1)))) \cdot (\mathrm{racahSum}\left(a, b, u, c, d, y\right)))) + ((\mathrm{rawGamma}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(c\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(d\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)\right)) \cdot (\mathrm{racahSum}\left(a, b, u, c, d, (y) - (2)\right))) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.racahSum_recurrence` (`✓ std3`). ∎

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The four-spin recurrence acts on the actual Racah sums. The two neighboring labels are y+2 and y-2 because labels are doubled spins.

**Definition 1.4 (zeroOffsets).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; (\mathrm{zeroOffsets}\left(a, b, q\right):\mathit{RacahOffsets}) = \mathrm{mk}\left(\mathrm{asInt}\left(\mathrm{int}\left(a\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(b\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(q\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(q\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(\mathrm{asNat}\left((a) + (b)\right)\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(q\right)\right), \mathrm{asInt}\left(\mathrm{int}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.zeroOffsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of zeroOffsets.

**Definition 1.5 (spinCasimir).**

$$\forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{spinCasimir}\left(x\right)\right) = (x) \cdot ((x) + (1))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.spinCasimir` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of spinCasimir.

**Definition 1.6 (jacobiDenominator).**

$$\forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{jacobiDenominator}\left(k\right)\right) = (((2) \cdot (k)) \cdot ((k) + (1))) \cdot (((2) \cdot (k)) + (1))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.jacobiDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of jacobiDenominator.

**Definition 1.7 (pivotLeftNumerator).**

$$\forall s \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall l \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{pivotLeftNumerator}\left(s, j, l, k\right)\right) = ((\mathrm{spinCasimir}\left(l\right)) - (\mathrm{spinCasimir}\left((k) - (s)\right))) \cdot ((\mathrm{spinCasimir}\left(((k) + (s)) + (1)\right)) - (\mathrm{spinCasimir}\left(j\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotLeftNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of pivotLeftNumerator.

**Definition 1.8 (pivotRightNumerator).**

$$\forall s \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall l \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{pivotRightNumerator}\left(s, j, l, k\right)\right) = ((\mathrm{spinCasimir}\left(l\right)) - (\mathrm{spinCasimir}\left(((k) - (s)) - (1)\right))) \cdot ((\mathrm{spinCasimir}\left((k) + (s)\right)) - (\mathrm{spinCasimir}\left(j\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotRightNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of pivotRightNumerator.

**Definition 1.9 (pivotLeft).**

$$\forall s \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall l \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{pivotLeft}\left(s, j, l, k\right)\right) = \mathrm{div}\left(\mathrm{pivotLeftNumerator}\left(s, j, l, k\right), ((2) \cdot ((k) + (1))) \cdot (((2) \cdot (k)) + (1))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of pivotLeft.

**Definition 1.10 (pivotRight).**

$$\forall s \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall l \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{pivotRight}\left(s, j, l, k\right)\right) = \mathrm{div}\left(\mathrm{pivotRightNumerator}\left(s, j, l, k\right), ((2) \cdot (k)) \cdot (((2) \cdot (k)) + (1))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of pivotRight.

**Definition 1.11 (endpointKernel).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{endpointKernel}\left(n, p, d, i\right)\right) = (((((\mathrm{rat}\left(\mathrm{Natfactorial}\left((i) + (d)\right)\right)) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(n\right)\right)) - (\mathrm{int}\left(i\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(p\right)\right)) - (\mathrm{int}\left(i\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(i\right)\right)) - (\mathrm{int}\left(d\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(n\right)\right)) + (\mathrm{int}\left(i\right))) + (1)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(p\right)\right)) + (\mathrm{int}\left(i\right))) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of endpointKernel.

**Definition 1.12 (endpointBase).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{endpointBase}\left(n, p, d, i\right)\right) = (((((\mathrm{rat}\left(\mathrm{Natfactorial}\left((i) + (d)\right)\right)) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(n\right)\right)) + (1)) - (\mathrm{int}\left(i\right))\right))) \cdot (\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(p\right)\right)) - (\mathrm{int}\left(i\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(i\right)\right)) + (1)) - (\mathrm{int}\left(d\right))\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(n\right)\right)) + (\mathrm{int}\left(i\right))) + (2)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(p\right)\right)) + (\mathrm{int}\left(i\right))) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of endpointBase.

**Definition 1.13 (endpointConstant).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{endpointConstant}\left(n, p, d\right)\right) = ((((((\mathrm{rat}\left(\mathrm{Natfactorial}\left((n) - (d)\right)\right)) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(p\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((p) - (d)\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(n\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(((n) + (p)) + (1)\right)\right))) \cdot (\mathrm{invFactorial}\left(\mathrm{int}\left(d\right)\right))) \cdot (\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(n\right)\right)) + (\mathrm{int}\left(p\right))) - (\mathrm{int}\left(d\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of endpointConstant.

**Definition 1.14 (signedEndpointConstant).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{signedEndpointConstant}\left(n, p, d\right)\right) = ((\mathrm{rat}\left(\mathrm{Natfactorial}\left((n) - (d)\right)\right)) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((p) - (d)\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(((n) + (p)) + (1)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of signedEndpointConstant.

**Definition 1.15 (endpointWeight).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{endpointWeight}\left(n, p, d, i\right)\right) = ((\mathrm{endpointConstant}\left(n, p, d\right)) \cdot (((2) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right))) + (1))) \cdot (\mathrm{endpointKernel}\left(n, p, d, i\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of endpointWeight.

**Definition 1.16 (signedEndpointWeight).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{signedEndpointWeight}\left(n, p, d, i\right)\right) = ((((-1)^{i}) \cdot (\mathrm{signedEndpointConstant}\left(n, p, d\right))) \cdot (((2) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right))) + (1))) \cdot (\mathrm{endpointKernel}\left(n, p, d, i\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of signedEndpointWeight.

**Definition 1.17 (endpointFlux).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{endpointFlux}\left(n, p, d, i\right)\right) = \mathrm{div}\left(-\left((((((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) \cdot ((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) - (\mathrm{rat}\left(d\right)))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(p\right)\right)) + (\mathrm{rat}\left(i\right))) + (1))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (\mathrm{rat}\left(i\right))) + (2))) \cdot (\mathrm{endpointConstant}\left((n) + (1), p, d\right))) \cdot (\mathrm{endpointKernel}\left((n) + (1), p, d, i\right))\right), ((((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (1)) - (\mathrm{rat}\left(d\right))) \cdot ((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (1))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (\mathrm{rat}\left(p\right))) + (2))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointFlux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of endpointFlux.

**Definition 1.18 (signedEndpointFlux).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{signedEndpointFlux}\left(n, p, d, i\right)\right) = \mathrm{div}\left(-\left(((((((-1)^{i}) \cdot ((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) - (\mathrm{rat}\left(d\right)))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(p\right)\right)) + (\mathrm{rat}\left(i\right))) + (1))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (\mathrm{rat}\left(i\right))) + (2))) \cdot (\mathrm{signedEndpointConstant}\left((n) + (1), p, d\right))) \cdot (\mathrm{endpointKernel}\left((n) + (1), p, d, i\right))\right), (((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (1)) - (\mathrm{rat}\left(d\right))) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right)) + (\mathrm{rat}\left(p\right))) + (2))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointFlux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of signedEndpointFlux.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointBase`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointConstant`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointFlux`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointKernel`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.endpointWeight`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.four_spin_raw_recurrence`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.jacobiDenominator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotLeft`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotLeftNumerator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotRight`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.pivotRightNumerator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.racahOffsets`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.racahSum_recurrence`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointConstant`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointFlux`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.signedEndpointWeight`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.spinCasimir`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence.zeroOffsets`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Expansion](Expansion.md)
