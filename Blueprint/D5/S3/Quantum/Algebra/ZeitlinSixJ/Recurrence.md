# Zeitlin Six-J Recurrence

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Definition 1.1 (channelLabel).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asNat}\left(\mathrm{channelLabel}\left(n, j, l, t\right)\right) = (\mathrm{channelBase}\left(n, j, l\right)) + ((2) \cdot (t))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.channelLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of channelLabel.

**Definition 1.2 (upperBand).**

$$\forall m \in \mathit{Nat},\; \forall e \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; (\mathrm{upperBand}\left(m, e\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right)) = ij\mapsto(\mathrm{ite}\left((\mathrm{val}\left(i\right)) + (1) = \mathrm{val}\left(j\right), e\left(i\right), 0\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.upperBand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of upperBand.

**Definition 1.3 (jacobiMatrix).**

$$\forall m \in \mathit{Nat},\; \forall a \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; \forall e \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; (\mathrm{jacobiMatrix}\left(m, a, e\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right)) = ((\mathrm{Matrixdiagonal}\left(a\right)) + (\mathrm{upperBand}\left(m, e\right))) + (\mathrm{transpose}\left(\mathrm{upperBand}\left(m, e\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.jacobiMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of jacobiMatrix.

**Definition 1.4 (physicalU).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalU}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = ki\mapsto((\mathrm{Realsqrt}\left((\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((\mathrm{channelLabel}\left(n, j, l, \mathrm{val}\left(k\right)\right)) + (1)\right)\right)\right)) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left(((2) \cdot (((l) - (j)) + (\mathrm{val}\left(i\right)))) + (1)\right)\right)\right))\right)) \cdot (\mathrm{sixJ}\left(n, n, (2) \cdot (((l) - (j)) + (\mathrm{val}\left(i\right))), (2) \cdot (j), (2) \cdot (l), \mathrm{channelLabel}\left(n, j, l, \mathrm{val}\left(k\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.physicalU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalU.

**Definition 1.5 (normalizedSixJ).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall u \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{normalizedSixJ}\left(a, b, u, c, d, y\right)\right) = (\mathrm{Realsqrt}\left((\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((y) + (1)\right)\right)\right)) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((u) + (1)\right)\right)\right))\right)) \cdot (\mathrm{sixJ}\left(a, b, u, c, d, y\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.normalizedSixJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of normalizedSixJ.

**Definition 1.6 (normalizedUpper).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{normalizedUpper}\left(a, b, c, d, y\right)\right) = \mathrm{div}\left((\mathrm{recurrenceUpperCoefficient}\left(a, b, c, d, y\right)) \cdot (\mathrm{Realsqrt}\left(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((y) + (1)\right)\right)\right)\right)), \mathrm{Realsqrt}\left(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((y) + (3)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.normalizedUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of normalizedUpper.

**Definition 1.7 (recurrenceDiagonalQ).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{recurrenceDiagonalQ}\left(a, b, c, d, y\right)\right) = \mathrm{ite}\left(y = 0, ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right)) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right)) + (1))) + ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right)) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right)) + (1))), \mathrm{rawDiagonal}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(c\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(d\right)\right), 2\right), \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.recurrenceDiagonalQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of recurrenceDiagonalQ.

**Definition 1.8 (finiteSixJMatrix).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall base \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall iota \in \mathit{Type},\; \forall us \in \mathit{iota} \to \mathit{Nat},\; (\mathrm{finiteSixJMatrix}\left(a, b, c, d, \mathit{base}, m, \mathit{iota}, \mathit{us}\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathit{iota}, \mathit{Real}\right)) = ki\mapsto(\mathrm{normalizedSixJ}\left(a, b, \mathit{us}\left(i\right), c, d, (\mathit{base}) + ((2) \cdot (\mathrm{val}\left(k\right)))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of finiteSixJMatrix.

**Definition 1.9 (finiteSixJJacobi).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall base \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; (\mathrm{finiteSixJJacobi}\left(a, b, c, d, \mathit{base}, m\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right)) = \mathrm{jacobiMatrix}\left(m, k\mapsto(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{recurrenceDiagonalQ}\left(a, b, c, d, (\mathit{base}) + ((2) \cdot (\mathrm{val}\left(k\right)))\right)\right)\right)), k\mapsto(\mathrm{normalizedUpper}\left(a, b, c, d, (\mathit{base}) + ((2) \cdot (\mathrm{val}\left(k\right)))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJJacobi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of finiteSixJJacobi.

**Lemma 1.10 (finiteSixJ action).**

$$\forall iota \in \mathit{Type},\; [\mathrm{Fintype}\left(\mathit{iota}\right)],[\mathrm{DecidableEq}\left(\mathit{iota}\right)],\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall base \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall us \in \mathit{iota} \to \mathit{Nat},\; (\forall k \in \mathrm{Fin}\left((m) + (1)\right),\; \forall i \in \mathit{iota},\; \mathrm{admissible}\left(a, b, \mathit{us}\left(i\right), c, d, (\mathit{base}) + ((2) \cdot (\mathrm{val}\left(k\right)))\right)) \Rightarrow ((\forall i \in \mathit{iota},\; (2 \le \mathit{base}) \Rightarrow (\mathrm{normalizedSixJ}\left(a, b, \mathit{us}\left(i\right), c, d, (\mathit{base}) - (2)\right) = 0)) \Rightarrow ((\forall i \in \mathit{iota},\; \mathrm{normalizedSixJ}\left(a, b, \mathit{us}\left(i\right), c, d, ((\mathit{base}) + ((2) \cdot (m))) + (2)\right) = 0) \Rightarrow ((\mathrm{finiteSixJJacobi}\left(a, b, c, d, \mathit{base}, m\right)) \cdot (\mathrm{finiteSixJMatrix}\left(a, b, c, d, \mathit{base}, m, \mathit{us}\right)) = (\mathrm{finiteSixJMatrix}\left(a, b, c, d, \mathit{base}, m, \mathit{us}\right)) \cdot (\mathrm{diagonal}\left(i\mapsto(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathit{us}\left(i\right)\right)\right), 2\right)) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathit{us}\left(i\right)\right)\right), 2\right)) + (1))\right)\right)\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJ_action` (`✓ std3`). ∎

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The triangle-normalized Racah recurrence gives the finite Jacobi action. The zero, half-spin and interior cases and both omitted edges are all included.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.channelLabel`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJJacobi`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.finiteSixJ_action`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.jacobiMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.normalizedSixJ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.normalizedUpper`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.physicalU`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.recurrenceDiagonalQ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence.upperBand`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint](Endpoint.md)
