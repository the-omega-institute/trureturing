# Zeitlin Six-J Inverse

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Theorem 1.1 (inverse moment open).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (2 \le N) \Rightarrow (((1 \le j) \land (j < N)) \Rightarrow (((1 \le l) \land (l < N)) \Rightarrow ((j \ne l) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), \mathrm{casimir}\left((i) + (1)\right)\right)) \cdot ((\mathrm{W}\left(N, (i) + (1), j, l\right))^{2})) = \mathrm{div}\left(1, ((\mathrm{asReal}\left(\mathrm{real}\left(N\right)\right)) \cdot (\left|(\mathrm{asReal}\left(\mathrm{real}\left(j\right)\right)) - (\mathrm{real}\left(l\right))\right|)) \cdot (((\mathrm{real}\left(j\right)) + (\mathrm{real}\left(l\right))) + (1))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.inverse_moment_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity (2.10) holds for all distinct positive j and l below N. The diagonal Green entry at the central spin is the reciprocal N times the Casimir difference.

**Definition 1.2 (indexParity).**

$$\forall m \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; (\mathrm{indexParity}\left(m, b\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right)) = \mathrm{diagonal}\left(i\mapsto((\mathrm{asReal}\left(-1\right))^{(b) + (\mathrm{val}\left(i\right))})\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.indexParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of indexParity.

**Lemma 1.3 (symmetric jacobi intertwiner unique).**

$$\forall m \in \mathit{Nat},\; \forall a \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; \forall e \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; \forall d \in \mathrm{Fin}\left((m) + (1)\right) \to \mathit{Real},\; \forall X \in \mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right),\; \forall Z \in \mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right),\; (\forall t \in \mathrm{Fin}\left(m\right),\; e\left(\mathrm{castSucc}\left(t\right)\right) \ne 0) \Rightarrow (((\mathrm{jacobiMatrix}\left(m, a, e\right)) \cdot (X) = (X) \cdot (\mathrm{diagonal}\left(d\right))) \Rightarrow (((\mathrm{jacobiMatrix}\left(m, a, e\right)) \cdot (Z) = (Z) \cdot (\mathrm{diagonal}\left(d\right))) \Rightarrow ((\mathrm{transpose}\left(X\right) = X) \Rightarrow ((\mathrm{transpose}\left(Z\right) = Z) \Rightarrow ((X\left(\mathrm{Finlast}\left(m\right), \mathrm{Finlast}\left(m\right)\right) = Z\left(\mathrm{Finlast}\left(m\right), \mathrm{Finlast}\left(m\right)\right)) \Rightarrow (X = Z))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.symmetric_jacobi_intertwiner_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A connected Jacobi matrix determines each eigen-column from its last coordinate by reverse induction. Symmetry and the last diagonal entry therefore determine the whole intertwiner.

**Definition 1.4 (physicalC0).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{physicalC0}\left(n, j, l\right)\right) = ((((2) \cdot (\mathrm{div}\left(\mathrm{asReal}\left(\mathrm{real}\left(n\right)\right), 2\right))) \cdot ((\mathrm{div}\left(\mathrm{asReal}\left(\mathrm{real}\left(n\right)\right), 2\right)) + (1))) + (\mathrm{casimir}\left(j\right))) + (\mathrm{casimir}\left(l\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalC0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalC0.

**Definition 1.5 (physicalX).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalX}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = ((\mathrm{physicalU}\left(n, j, l\right)) \cdot (\mathrm{indexParity}\left(\mathrm{channelWidth}\left(n, j, l\right), (l) - (j)\right))) \cdot (\mathrm{transpose}\left(\mathrm{physicalU}\left(n, j, l\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalX.

**Definition 1.6 (physicalM).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalM}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = ((\mathrm{smul}\left(\mathrm{physicalC0}\left(n, j, l\right), 1\right)) - (\mathrm{diagonal}\left(\mathrm{physicalCasimir}\left(n, j, l\right)\right))) - (\mathrm{physicalT}\left(n, j, l\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalM.

**Definition 1.7 (physicalV).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalV}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{finiteSixJMatrix}\left(n, (2) \cdot (l), n, (2) \cdot (j), \mathrm{channelBase}\left(n, j, l\right), \mathrm{channelWidth}\left(n, j, l\right), h:\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right)\mapsto(\mathrm{channelLabel}\left(n, j, l, \mathrm{val}\left(h\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalV.

**Definition 1.8 (physicalTprime).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalTprime}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{finiteSixJJacobi}\left(n, (2) \cdot (l), n, (2) \cdot (j), \mathrm{channelBase}\left(n, j, l\right), \mathrm{channelWidth}\left(n, j, l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalTprime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalTprime.

**Definition 1.9 (physicalZ).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalZ}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{smul}\left((\mathrm{asReal}\left(-1\right))^{\mathrm{channelBase}\left(n, j, l\right)}, ((\mathrm{indexParity}\left(\mathrm{channelWidth}\left(n, j, l\right), 0\right)) \cdot (\mathrm{physicalV}\left(n, j, l\right))) \cdot (\mathrm{indexParity}\left(\mathrm{channelWidth}\left(n, j, l\right), 0\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalZ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalZ.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.indexParity`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.inverse_moment_open`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalC0`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalM`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalTprime`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalV`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalX`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.physicalZ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse.symmetric_jacobi_intertwiner_unique`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/SpectralInverse](SpectralInverse.md)
