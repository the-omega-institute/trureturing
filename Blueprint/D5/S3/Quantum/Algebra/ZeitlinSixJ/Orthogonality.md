# Zeitlin Six-J Orthogonality

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Definition 1.1 (physicalT).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalT}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{finiteSixJJacobi}\left(n, n, (2) \cdot (j), (2) \cdot (l), \mathrm{channelBase}\left(n, j, l\right), \mathrm{channelWidth}\left(n, j, l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalT.

**Definition 1.2 (physicalH).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalH}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{finiteSixJJacobi}\left(n, (2) \cdot (l), (2) \cdot (j), n, (2) \cdot ((l) - (j)), \mathrm{channelWidth}\left(n, j, l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalH.

**Definition 1.3 (physicalCasimir).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall k \in \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right),\; \mathrm{asReal}\left(\mathrm{physicalCasimir}\left(n, j, l, k\right)\right) = \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{channelLabel}\left(n, j, l, \mathrm{val}\left(k\right)\right)\right)\right), 2\right)) \cdot ((\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{channelLabel}\left(n, j, l, \mathrm{val}\left(k\right)\right)\right)\right), 2\right)) + (1))\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalCasimir` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalCasimir.

**Lemma 1.4 (physicalU orthogonality).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (j \le n) \Rightarrow ((l \le n) \Rightarrow ((j \le l) \Rightarrow ((\mathrm{physicalU}\left(n, j, l\right)) \cdot (\mathrm{transpose}\left(\mathrm{physicalU}\left(n, j, l\right)\right)) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalU_orthogonality` (`✓ std3`). ∎

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The physical Racah matrix is orthogonal. Its two recurrences, injective Casimir labels, nonzero Jacobi edges and stretched endpoint norm establish its Gram matrix.

**Definition 1.5 (greenColumn).**

$$\forall a \in \mathit{Nat} \to \mathit{Real},\; \forall e \in \mathit{Nat} \to \mathit{Real},\; \forall L \in \mathit{Nat} \to \mathit{Real},\; \forall R \in \mathit{Nat} \to \mathit{Real},\; \forall k \in \mathit{Nat},\; \forall h \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{greenColumn}\left(a, e, L, R, k, h\right)\right) = (\mathrm{inv}\left(((L\left(h\right)) + (R\left(h\right))) - (a\left(h\right))\right)) \cdot (\mathrm{ite}\left(k \le h, \prod_{t\in\mathrm{Ico}\left(k, h\right)}(\mathrm{div}\left(-e\left(t\right), L\left(t\right)\right)), \prod_{t\in\mathrm{Ico}\left(h, k\right)}(\mathrm{div}\left(-e\left(t\right), R\left((t) + (1)\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.greenColumn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of greenColumn.

**Definition 1.6 (greenMatrix).**

$$\forall m \in \mathit{Nat},\; \forall a \in \mathit{Nat} \to \mathit{Real},\; \forall e \in \mathit{Nat} \to \mathit{Real},\; \forall L \in \mathit{Nat} \to \mathit{Real},\; \forall R \in \mathit{Nat} \to \mathit{Real},\; (\mathrm{greenMatrix}\left(m, a, e, L, R\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((m) + (1)\right), \mathrm{Fin}\left((m) + (1)\right), \mathit{Real}\right)) = kh\mapsto(\mathrm{greenColumn}\left(a, e, L, R, \mathrm{val}\left(k\right), \mathrm{val}\left(h\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.greenMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of greenMatrix.

**Lemma 1.7 (jacobi green inverse).**

$$\forall m \in \mathit{Nat},\; \forall a \in \mathit{Nat} \to \mathit{Real},\; \forall e \in \mathit{Nat} \to \mathit{Real},\; \forall L \in \mathit{Nat} \to \mathit{Real},\; \forall R \in \mathit{Nat} \to \mathit{Real},\; (\forall k \in \mathit{Nat},\; (k \le m) \Rightarrow (L\left(k\right) \ne 0)) \Rightarrow ((\forall k \in \mathit{Nat},\; (k \le m) \Rightarrow (R\left(k\right) \ne 0)) \Rightarrow ((\forall k \in \mathit{Nat},\; (k \le m) \Rightarrow (((L\left(k\right)) + (R\left(k\right))) - (a\left(k\right)) \ne 0)) \Rightarrow ((a\left(0\right) = L\left(0\right)) \Rightarrow ((a\left(m\right) = R\left(m\right)) \Rightarrow ((\forall k \in \mathit{Nat},\; (0 < k) \Rightarrow ((k \le m) \Rightarrow ((e\left((k) - (1)\right))^{2} = (L\left((k) - (1)\right)) \cdot ((a\left(k\right)) - (L\left(k\right)))))) \Rightarrow ((\forall k \in \mathit{Nat},\; (k < m) \Rightarrow ((e\left(k\right))^{2} = (R\left((k) + (1)\right)) \cdot ((a\left(k\right)) - (R\left(k\right))))) \Rightarrow ((\mathrm{jacobiMatrix}\left(m, k\mapsto(a\left(\mathrm{val}\left(k\right)\right)), k\mapsto(e\left(\mathrm{val}\left(k\right)\right))\right)) \cdot (\mathrm{greenMatrix}\left(m, a, e, L, R\right)) = 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.jacobi_green_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two one-sided pivot recurrences and boundary conditions construct the inverse of the finite Jacobi matrix. The product formula solves the homogeneous equation on each side and has unit diagonal residual.

**Definition 1.8 (channelSpin).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{channelSpin}\left(n, j, l, t\right)\right) = \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{channelLabel}\left(n, j, l, t\right)\right)\right), 2\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.channelSpin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of channelSpin.

**Definition 1.9 (physicalA).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{physicalA}\left(n, j, l, t\right)\right) = \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{recurrenceDiagonalQ}\left(n, n, (2) \cdot (j), (2) \cdot (l), \mathrm{channelLabel}\left(n, j, l, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalA.

**Definition 1.10 (physicalE).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{physicalE}\left(n, j, l, t\right)\right) = \mathrm{normalizedUpper}\left(n, n, (2) \cdot (j), (2) \cdot (l), \mathrm{channelLabel}\left(n, j, l, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalE.

**Definition 1.11 (physicalLP).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{physicalLP}\left(n, j, l, t\right)\right) = \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{pivotLeft}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right), 2\right), \mathrm{rat}\left(j\right), \mathrm{rat}\left(l\right), \mathrm{channelSpin}\left(n, j, l, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalLP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalLP.

**Definition 1.12 (physicalRP).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{physicalRP}\left(n, j, l, t\right)\right) = \mathrm{asReal}\left(\mathrm{real}\left(\mathrm{pivotRight}\left(\mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(n\right)\right), 2\right), \mathrm{rat}\left(j\right), \mathrm{rat}\left(l\right), \mathrm{channelSpin}\left(n, j, l, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalRP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalRP.

**Definition 1.13 (physicalG).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalG}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = \mathrm{greenMatrix}\left(\mathrm{channelWidth}\left(n, j, l\right), \mathrm{physicalA}\left(n, j, l\right), \mathrm{physicalE}\left(n, j, l\right), \mathrm{physicalLP}\left(n, j, l\right), \mathrm{physicalRP}\left(n, j, l\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalG.

**Definition 1.14 (physicalSpectralInverse).**

$$\forall n \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; (\mathrm{physicalSpectralInverse}\left(n, j, l\right):\mathrm{Matrix}\left(\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right), \mathit{Real}\right)) = ((\mathrm{physicalU}\left(n, j, l\right)) \cdot (\mathrm{diagonal}\left(i:\mathrm{Fin}\left((\mathrm{channelWidth}\left(n, j, l\right)) + (1)\right)\mapsto(\mathrm{inv}\left(\mathrm{casimir}\left(((l) - (j)) + (\mathrm{val}\left(i\right))\right)\right))\right))) \cdot (\mathrm{transpose}\left(\mathrm{physicalU}\left(n, j, l\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalSpectralInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of physicalSpectralInverse.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.channelSpin`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.greenColumn`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.greenMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.jacobi_green_inverse`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalA`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalCasimir`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalE`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalG`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalH`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalLP`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalRP`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalSpectralInverse`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalT`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Orthogonality.physicalU_orthogonality`
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Recurrence](Recurrence.md)
