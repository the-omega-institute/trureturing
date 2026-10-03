# Zeitlin Six-J Endpoint

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Lemma 1.1 (endpoint normalization).**

$$\forall n \in \mathit{Nat},\; \forall p \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; (d \le n) \Rightarrow ((d \le p) \Rightarrow (\sum_{i\in\mathrm{range}\left((p) + (1)\right)}(\mathrm{endpointWeight}\left(n, p, d, i\right)) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.endpoint_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stretched weights sum to one for every n at least d. The exact flux recurrence and the initial normalization give a finite induction.

**Lemma 1.2 (signed stretched endpoint match).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; (d \le n) \Rightarrow (\sum_{i\in\mathrm{range}\left((((2) \cdot (j)) + (d)) + (1)\right)}(((\mathrm{asReal}\left(-1\right))^{i}) \cdot (((\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left(((n) + ((2) \cdot (j))) + (1)\right)\right)\right)) \cdot (((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(i\right)\right))) + (1))) \cdot ((\mathrm{sixJ}\left(n, n, (2) \cdot (i), (2) \cdot (j), (2) \cdot ((j) + (d)), (n) + ((2) \cdot (j))\right))^{2}))) = (((\mathrm{asReal}\left(-1\right))^{(n) + ((2) \cdot (j))}) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left(((n) + ((2) \cdot (j))) + (1)\right)\right)\right))) \cdot (\mathrm{sixJ}\left(n, (2) \cdot ((j) + (d)), (n) + ((2) \cdot (j)), n, (2) \cdot (j), (n) + ((2) \cdot (j))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.signed_stretched_endpoint_match` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating squared stretched row equals the endpoint entry of the second Racah matrix, with the exact Racah phase.

**Lemma 1.3 (dual intertwining orthogonality).**

$$\forall iota \in \mathit{Type},\; [\mathrm{Fintype}\left(\mathit{iota}\right)],[\mathrm{DecidableEq}\left(\mathit{iota}\right)],\forall m \in \mathit{Nat},\; \forall U \in \mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathit{iota}, \mathit{Real}\right),\; \forall T \in \mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right),\; \forall H \in \mathrm{Matrix}\left(\mathit{iota}, \mathit{iota}, \mathit{Real}\right),\; \forall dk \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; \forall li \in \mathit{iota} \to \mathit{Real},\; (\mathrm{FunctionInjective}\left(\mathit{dk}\right)) \Rightarrow ((\mathrm{transpose}\left(T\right) = T) \Rightarrow ((\mathrm{transpose}\left(H\right) = H) \Rightarrow (((T) \cdot (U) = (U) \cdot (\mathrm{diagonal}\left(\mathit{li}\right))) \Rightarrow (((\mathrm{diagonal}\left(\mathit{dk}\right)) \cdot (U) = (U) \cdot (H)) \Rightarrow ((\forall t \in \mathrm{Fin}\left(m\right),\; T\left(\mathrm{castSucc}\left(t\right), \mathrm{succ}\left(t\right)\right) \ne 0) \Rightarrow ((\left((U) \cdot (\mathrm{transpose}\left(U\right))\right)\left(\mathrm{Finlast}\left(m\right)\right)\left(\mathrm{Finlast}\left(m\right)\right) = 1) \Rightarrow ((U) \cdot (\mathrm{transpose}\left(U\right)) = 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.dual_intertwining_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two intertwining equations force the Gram matrix to commute with an injective diagonal and a connected Jacobi matrix. It is diagonal and its adjacent entries coincide; the endpoint normalization fixes them to one.

**Definition 1.4 (jacobiEdgeSq).**

$$\forall s \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall l \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{jacobiEdgeSq}\left(s, j, l, k\right)\right) = \mathrm{div}\left((((((k)^{2}) - (((s) - (j))^{2})) \cdot (((((s) + (j)) + (1))^{2}) - ((k)^{2}))) \cdot (((k)^{2}) - (((s) - (l))^{2}))) \cdot (((((s) + (l)) + (1))^{2}) - ((k)^{2})), (((4) \cdot ((k)^{2})) \cdot (((2) \cdot (k)) - (1))) \cdot (((2) \cdot (k)) + (1))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.jacobiEdgeSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of jacobiEdgeSq.

**Definition 1.5 (triangleSqProduct).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall u \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{triangleSqProduct}\left(a, b, u, c, d, y\right)\right) = (((\mathrm{deltaSq}\left(a, b, u\right)) \cdot (\mathrm{deltaSq}\left(a, d, y\right))) \cdot (\mathrm{deltaSq}\left(c, b, y\right))) \cdot (\mathrm{deltaSq}\left(c, d, u\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.triangleSqProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of triangleSqProduct.

**Definition 1.6 (raisingNumerator).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{raisingNumerator}\left(a, b, c, d, y\right)\right) = ((((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)) + (1))^{2}) - ((\mathrm{div}\left((\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right)) - (\mathrm{rat}\left(d\right)), 2\right))^{2})) \cdot ((((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)) + (1))^{2}) - ((\mathrm{div}\left((\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right)) - (\mathrm{rat}\left(c\right)), 2\right))^{2}))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.raisingNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of raisingNumerator.

**Definition 1.7 (raisingDenominator).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{raisingDenominator}\left(a, b, c, d, y\right)\right) = ((((\mathrm{div}\left((\mathrm{asRat}\left(\mathrm{rat}\left(a\right)\right)) + (\mathrm{rat}\left(d\right)), 2\right)) + (1))^{2}) - (((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)) + (1))^{2})) \cdot ((((\mathrm{div}\left((\mathrm{asRat}\left(\mathrm{rat}\left(b\right)\right)) + (\mathrm{rat}\left(c\right)), 2\right)) + (1))^{2}) - (((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)) + (1))^{2}))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.raisingDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of raisingDenominator.

**Definition 1.8 (recurrenceUpperCoefficient).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{recurrenceUpperCoefficient}\left(a, b, c, d, y\right)\right) = \mathrm{div}\left(\mathrm{Realsqrt}\left(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left((\mathrm{raisingNumerator}\left(a, b, c, d, y\right)) \cdot (\mathrm{raisingDenominator}\left(a, b, c, d, y\right))\right)\right)\right)\right), \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left(((2) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right)) + (1))) \cdot (((2) \cdot (\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right))) + (1))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.recurrenceUpperCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of recurrenceUpperCoefficient.

**Definition 1.9 (recurrenceLowerCoefficient).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall y \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{recurrenceLowerCoefficient}\left(a, b, c, d, y\right)\right) = \mathrm{div}\left(\mathrm{Realsqrt}\left(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left((\mathrm{raisingNumerator}\left(a, b, c, d, (y) - (2)\right)) \cdot (\mathrm{raisingDenominator}\left(a, b, c, d, (y) - (2)\right))\right)\right)\right)\right), \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left(((2) \cdot (\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right))) \cdot (((2) \cdot (\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(y\right)\right), 2\right))) + (1))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.recurrenceLowerCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of recurrenceLowerCoefficient.

**Definition 1.10 (channelWidth).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{asNat}\left(\mathrm{channelWidth}\left(n, j, l\right)\right) = (\mathrm{min}\left(n, (j) + (l)\right)) - ((l) - (j))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.channelWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of channelWidth.

**Definition 1.11 (channelBase).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{asNat}\left(\mathrm{channelBase}\left(n, j, l\right)\right) = ((\mathrm{max}\left(n, (j) + (l)\right)) - (\mathrm{min}\left(n, (j) + (l)\right))) + ((l) - (j))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.channelBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of channelBase.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.channelBase`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.channelWidth`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.dual_intertwining_orthogonality`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.endpoint_normalization`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.jacobiEdgeSq`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.raisingDenominator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.raisingNumerator`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.recurrenceLowerCoefficient`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.recurrenceUpperCoefficient`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.signed_stretched_endpoint_match`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.triangleSqProduct`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/RawRecurrence](RawRecurrence.md)
