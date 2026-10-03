# Zeitlin Six-J Racah

## Abstract

Racah finite sums and the Zeitlin six-j identities.

Nat, Int, Rat and Real denote the natural numbers, integers, rationals and reals; Type is an arbitrary Lean universe. Function names in formulas omit dots and underscores. In a defining equation every data and type parameter is displayed explicitly, including implicit type parameters; typeclass dictionaries stay anonymous. natDiv is the floor quotient on natural numbers, and subtraction in Nat is truncated at zero. intDiv is the signed integer quotient, div is field division, mod is natural remainder, inv is field or matrix inverse and smul is scalar multiplication. asNat, asInt, asRat and asReal record the indicated type or cast; int, rat and real are scalar casts. val maps a Fin index to its natural value. Fin constructors display their value coordinate; their proof coordinate is irrelevant. range(n) is {0,...,n-1}; Ico(a,b) is {a,...,b-1}. ite selects its first or second value according to its condition. Matrix products are ordinary finite matrix products and transpose is ordinary transpose. A function displayed using a mapsto has the domain and codomain in the defining type. Anonymous square brackets retain the indicated Lean instance assumptions.

**Definition 1.1 (triangle).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; (\mathrm{triangle}\left(a, b, c\right):\mathit{Prop}) = \left((a \le (b) + (c)) \land ((b \le (a) + (c)) \land ((c \le (a) + (b)) \land (\mathrm{mod}\left(((a) + (b)) + (c), 2\right) = 0)))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.triangle` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of triangle.

**Definition 1.2 (triangleDecidable).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; (\mathrm{triangleDecidable}\left(a, b, c\right):\mathrm{Decidable}\left(\mathrm{triangle}\left(a, b, c\right)\right)) = \mathrm{inferInstanceAs}\left(\mathrm{Decidable}\left((a \le (b) + (c)) \land ((b \le (a) + (c)) \land ((c \le (a) + (b)) \land (\mathrm{mod}\left(((a) + (b)) + (c), 2\right) = 0)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.triangleDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of triangleDecidable.

**Definition 1.3 (admissible).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; (\mathrm{admissible}\left(a, b, c, d, e, f\right):\mathit{Prop}) = \left((\mathrm{triangle}\left(a, b, c\right)) \land ((\mathrm{triangle}\left(a, e, f\right)) \land ((\mathrm{triangle}\left(d, b, f\right)) \land (\mathrm{triangle}\left(d, e, c\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.admissible` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of admissible.

**Definition 1.4 (admissibleDecidable).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; (\mathrm{admissibleDecidable}\left(a, b, c, d, e, f\right):\mathrm{Decidable}\left(\mathrm{admissible}\left(a, b, c, d, e, f\right)\right)) = \mathrm{inferInstanceAs}\left(\mathrm{Decidable}\left((\mathrm{triangle}\left(a, b, c\right)) \land ((\mathrm{triangle}\left(a, e, f\right)) \land ((\mathrm{triangle}\left(d, b, f\right)) \land (\mathrm{triangle}\left(d, e, c\right))))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.admissibleDecidable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of admissibleDecidable.

**Definition 1.5 (deltaSq).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{deltaSq}\left(a, b, c\right)\right) = \mathrm{div}\left(((\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{Natfactorial}\left(\mathrm{natDiv}\left(((a) + (b)) - (c), 2\right)\right)\right)\right)) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(\mathrm{natDiv}\left(((a) + (c)) - (b), 2\right)\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(\mathrm{natDiv}\left(((b) + (c)) - (a), 2\right)\right)\right)), \mathrm{rat}\left(\mathrm{Natfactorial}\left((\mathrm{natDiv}\left(((a) + (b)) + (c), 2\right)) + (1)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of deltaSq.

**Definition 1.6 (lower).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{asNat}\left(\mathrm{lower}\left(a, b, c, d, e, f\right)\right) = \mathrm{max}\left(\mathrm{max}\left(\mathrm{natDiv}\left(((a) + (b)) + (c), 2\right), \mathrm{natDiv}\left(((a) + (e)) + (f), 2\right)\right), \mathrm{max}\left(\mathrm{natDiv}\left(((d) + (b)) + (f), 2\right), \mathrm{natDiv}\left(((d) + (e)) + (c), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.lower` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of lower.

**Definition 1.7 (upper).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{asNat}\left(\mathrm{upper}\left(a, b, c, d, e, f\right)\right) = \mathrm{min}\left(\mathrm{natDiv}\left((((a) + (b)) + (d)) + (e), 2\right), \mathrm{min}\left(\mathrm{natDiv}\left((((b) + (c)) + (e)) + (f), 2\right), \mathrm{natDiv}\left((((c) + (a)) + (f)) + (d), 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.upper` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of upper.

**Definition 1.8 (racahTerm).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \forall z \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahTerm}\left(a, b, c, d, e, f, z\right)\right) = \mathrm{div}\left(((\mathrm{asRat}\left(-1\right))^{z}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) + (1)\right)\right)), \mathrm{asRat}\left(((((((\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) - (\mathrm{natDiv}\left(((a) + (b)) + (c), 2\right))\right)\right)) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) - (\mathrm{natDiv}\left(((a) + (e)) + (f), 2\right))\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) - (\mathrm{natDiv}\left(((d) + (b)) + (f), 2\right))\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((z) - (\mathrm{natDiv}\left(((d) + (e)) + (c), 2\right))\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((\mathrm{natDiv}\left((((a) + (b)) + (d)) + (e), 2\right)) - (z)\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((\mathrm{natDiv}\left((((b) + (c)) + (e)) + (f), 2\right)) - (z)\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((\mathrm{natDiv}\left((((c) + (a)) + (f)) + (d), 2\right)) - (z)\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahTerm` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of racahTerm.

**Definition 1.9 (racahSum).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahSum}\left(a, b, c, d, e, f\right)\right) = \sum_{z\in\mathrm{range}\left((\mathrm{upper}\left(a, b, c, d, e, f\right)) + (1)\right)}(\mathrm{ite}\left(\mathrm{lower}\left(a, b, c, d, e, f\right) \le z, \mathrm{racahTerm}\left(a, b, c, d, e, f, z\right), 0\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahSum` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of racahSum.

**Definition 1.10 (sixJ).**

$$\forall a \in \mathit{Nat},\; \forall b \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall d \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \forall f \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{sixJ}\left(a, b, c, d, e, f\right)\right) = \mathrm{ite}\left(\mathrm{admissible}\left(a, b, c, d, e, f\right), (\mathrm{Realsqrt}\left(\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{asRat}\left((((\mathrm{deltaSq}\left(a, b, c\right)) \cdot (\mathrm{deltaSq}\left(a, e, f\right))) \cdot (\mathrm{deltaSq}\left(d, b, f\right))) \cdot (\mathrm{deltaSq}\left(d, e, c\right))\right)\right)\right)\right)) \cdot (\mathrm{asReal}\left(\mathrm{real}\left(\mathrm{racahSum}\left(a, b, c, d, e, f\right)\right)\right)), 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.sixJ` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of sixJ.

**Definition 1.11 (racahMonomial).**

$$\forall k \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahMonomial}\left(k, i\right)\right) = \mathrm{ite}\left(k \le i, \mathrm{div}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{Natfactorial}\left((i) + (k)\right)\right)\right), \mathrm{rat}\left(\mathrm{Natfactorial}\left((i) - (k)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of racahMonomial.

**Definition 1.12 (racahCoefficient).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahCoefficient}\left(N, j, k\right)\right) = ((((\mathrm{asRat}\left(-1\right))^{k}) \cdot (\mathrm{rat}\left(\mathrm{Natchoose}\left(j, k\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natchoose}\left((j) + (k), k\right)\right))) \cdot (\mathrm{div}\left((\mathrm{asRat}\left(\mathrm{rat}\left(N\right)\right)) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(((N) - (k)) - (1)\right)\right)), \mathrm{rat}\left(\mathrm{Natfactorial}\left((N) + (k)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of racahCoefficient.

**Definition 1.13 (racahPolynomial).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahPolynomial}\left(N, j, i\right)\right) = (1) + (\sum_{k\in\mathrm{range}\left(j\right)}((\mathrm{racahCoefficient}\left(N, j, (k) + (1)\right)) \cdot (\mathrm{racahMonomial}\left((k) + (1), i\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of racahPolynomial.

**Lemma 1.14 (polynomial harmonic).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; (2 \le N) \Rightarrow ((j < N) \Rightarrow (\sum_{i\in\mathrm{range}\left((N) - (1)\right)}((\mathrm{div}\left(((2) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right))) + (1), (\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{asNat}\left((i) + (1)\right)\right)\right)) \cdot ((\mathrm{rat}\left(\mathrm{asNat}\left((i) + (1)\right)\right)) + (1))\right)) \cdot ((1) - (\mathrm{racahPolynomial}\left(N, j, (i) + (1)\right)))) = (2) \cdot (\mathrm{harmonic}\left(j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.polynomial_harmonic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted terminating Racah polynomial sum equals twice the harmonic number. A finite antidifference and a binomial harmonic induction evaluate the sum.

**Definition 1.15 (W).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall l \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{W}\left(N, i, j, l\right)\right) = \mathrm{sixJ}\left((2) \cdot (i), (2) \cdot (j), (2) \cdot (l), (N) - (1), (N) - (1), (N) - (1)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.W` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Page 6, section 2.2: “To begin, for fixed N, we introduce the abbreviated notation below for certain six-j symbols that appear frequently throughout the paper:”. The defining equation below implements equation (2.6). Each sixJ label is twice the displayed spin; W(N,i,j,l) denotes the symbol with top row i,j,l and bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) denotes the symbol with top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2.

**Definition 1.16 (Wij).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{Wij}\left(N, i, j\right)\right) = \mathrm{sixJ}\left((2) \cdot (i), (N) - (1), (N) - (1), (2) \cdot (j), (N) - (1), (N) - (1)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.Wij` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

Page 6, section 2.2: “To begin, for fixed N, we introduce the abbreviated notation below for certain six-j symbols that appear frequently throughout the paper:”. The defining equation below implements equation (2.6). Each sixJ label is twice the displayed spin; W(N,i,j,l) denotes the symbol with top row i,j,l and bottom row (N−1)/2,(N−1)/2,(N−1)/2, and Wij(N,i,j) denotes the symbol with top row i,(N−1)/2,(N−1)/2 and bottom row j,(N−1)/2,(N−1)/2.

**Definition 1.17 (casimir).**

$$\forall i \in \mathit{Nat},\; \mathrm{asReal}\left(\mathrm{casimir}\left(i\right)\right) = (\mathrm{asReal}\left(\mathrm{real}\left(i\right)\right)) \cdot ((\mathrm{real}\left(i\right)) + (1))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.casimir` (`✓ std3`).

*Citation.* Leandro Lichtenfelz, Klas Modin, Stephen C. Preston (2026). *Ricci curvature for hydrodynamics on the sphere*. DOI: [10.1007/s00220-025-05533-w](https://doi.org/10.1007/s00220-025-05533-w). URL: <https://arxiv.org/abs/2508.09833v1>.

*Commentary.*

The displayed equation is the defining expression of casimir.

**Definition 1.18 (newtonBasis).**

$$\forall k \in \mathit{Nat},\; \forall x \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{newtonBasis}\left(k, x\right)\right) = \prod_{r\in\mathrm{range}\left(k\right)}(((x) - (\mathrm{rat}\left(r\right))) \cdot (((x) + (\mathrm{rat}\left(r\right))) + (1)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.newtonBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of newtonBasis.

**Lemma 1.19 (recurrence unique).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall f \in \mathit{Nat} \to \mathit{Rat},\; \forall g \in \mathit{Nat} \to \mathit{Rat},\; (2 \le N) \Rightarrow ((f\left(0\right) = g\left(0\right)) \Rightarrow ((\forall i \in \mathit{Nat},\; ((i) + (1) < N) \Rightarrow (((((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) + (1)) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(N\right)\right))^{2}) - (\mathrm{rat}\left(((i) + (1))^{2}\right)))) \cdot ((f\left(i\right)) - (f\left((i) + (1)\right)))) + (((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(N\right)\right))^{2}) - (\mathrm{rat}\left((i)^{2}\right)))) \cdot ((f\left(i\right)) - (f\left((i) - (1)\right)))) = ((((2) \cdot (((2) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right))) + (1))) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(j\right)\right))) \cdot ((\mathrm{rat}\left(j\right)) + (1))) \cdot (f\left(i\right)))) \Rightarrow ((\forall i \in \mathit{Nat},\; ((i) + (1) < N) \Rightarrow (((((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) + (1)) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(N\right)\right))^{2}) - (\mathrm{rat}\left(((i) + (1))^{2}\right)))) \cdot ((g\left(i\right)) - (g\left((i) + (1)\right)))) + (((\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right)) \cdot (((\mathrm{asRat}\left(\mathrm{rat}\left(N\right)\right))^{2}) - (\mathrm{rat}\left((i)^{2}\right)))) \cdot ((g\left(i\right)) - (g\left((i) - (1)\right)))) = ((((2) \cdot (((2) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(i\right)\right))) + (1))) \cdot (\mathrm{asRat}\left(\mathrm{rat}\left(j\right)\right))) \cdot ((\mathrm{rat}\left(j\right)) + (1))) \cdot (g\left(i\right)))) \Rightarrow (\forall i \in \mathit{Nat},\; (i < N) \Rightarrow (f\left(i\right) = g\left(i\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.recurrence_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward coefficient does not vanish below N. Strong induction determines the whole finite sequence from its initial value and the difference equation.

**Definition 1.20 (certificatePolynomial).**

$$\forall N \in \mathit{Rat},\; \forall i \in \mathit{Rat},\; \forall j \in \mathit{Rat},\; \forall k \in \mathit{Rat},\; \mathrm{asRat}\left(\mathrm{certificatePolynomial}\left(N, i, j, k\right)\right) = (((((N)^{2}) - ((i) \cdot (((2) \cdot (j)) + (1)))) \cdot ((((i) + (1)) - (k))^{2})) + ((((2) \cdot (i)) \cdot (((N)^{2}) - ((j) \cdot (((i) + (j)) + (1))))) \cdot (((i) + (1)) - (k)))) + (((i) \cdot ((i) + (1))) \cdot (((N)^{2}) - ((j)^{2})))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.certificatePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of certificatePolynomial.

**Definition 1.21 (normalizedRacah).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{normalizedRacah}\left(N, i, j\right)\right) = (((((\mathrm{asRat}\left(-1\right))^{(((N) - (1)) + (i)) + (j)}) \cdot (\mathrm{rat}\left(N\right))) \cdot (\mathrm{deltaSq}\left((2) \cdot (i), (N) - (1), (N) - (1)\right))) \cdot (\mathrm{deltaSq}\left((2) \cdot (j), (N) - (1), (N) - (1)\right))) \cdot (\mathrm{racahSum}\left((2) \cdot (i), (N) - (1), (N) - (1), (2) \cdot (j), (N) - (1), (N) - (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.normalizedRacah` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of normalizedRacah.

**Definition 1.22 (invFactorial).**

$$\forall z \in \mathit{Int},\; \mathrm{asRat}\left(\mathrm{invFactorial}\left(z\right)\right) = \mathrm{ite}\left(0 \le z, \mathrm{inv}\left(\mathrm{asRat}\left(\mathrm{rat}\left(\mathrm{Natfactorial}\left(\mathrm{toNat}\left(z\right)\right)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.invFactorial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of invFactorial.

**Definition 1.23 (factorialKernel).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{factorialKernel}\left(N, i, j, k\right)\right) = ((((((\mathrm{asRat}\left(-1\right))^{k}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((((N) + (i)) + (j)) - (k)\right)\right))) \cdot ((\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(i\right)\right)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(j\right)\right)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left(\mathrm{asInt}\left(\mathrm{int}\left(k\right)\right)\right))^{2})) \cdot (\mathrm{invFactorial}\left(((((\mathrm{asInt}\left(\mathrm{int}\left(N\right)\right)) - (1)) + (\mathrm{int}\left(k\right))) - (\mathrm{int}\left(i\right))) - (\mathrm{int}\left(j\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.factorialKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of factorialKernel.

**Definition 1.24 (certificateBase).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{certificateBase}\left(N, i, j, k\right)\right) = ((((((\mathrm{asRat}\left(-1\right))^{k}) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left(((((N) + (i)) + (j)) - (k)) - (1)\right)\right))) \cdot ((\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(i\right)\right)) + (1)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(j\right)\right)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left(\mathrm{asInt}\left(\mathrm{int}\left(k\right)\right)\right))^{2})) \cdot (\mathrm{invFactorial}\left((((\mathrm{asInt}\left(\mathrm{int}\left(N\right)\right)) + (\mathrm{int}\left(k\right))) - (\mathrm{int}\left(i\right))) - (\mathrm{int}\left(j\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.certificateBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of certificateBase.

**Definition 1.25 (kernelFlux).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall k \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{kernelFlux}\left(N, i, j, k\right)\right) = (((((((\mathrm{asRat}\left(-1\right))^{k}) \cdot (\mathrm{certificatePolynomial}\left(\mathrm{rat}\left(N\right), \mathrm{rat}\left(i\right), \mathrm{rat}\left(j\right), \mathrm{rat}\left(k\right)\right))) \cdot (\mathrm{rat}\left(\mathrm{Natfactorial}\left((((N) + (i)) + (j)) - (k)\right)\right))) \cdot ((\mathrm{invFactorial}\left(((\mathrm{asInt}\left(\mathrm{int}\left(i\right)\right)) + (1)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(j\right)\right)) - (\mathrm{int}\left(k\right))\right))^{2})) \cdot ((\mathrm{invFactorial}\left((\mathrm{asInt}\left(\mathrm{int}\left(k\right)\right)) - (1)\right))^{2})) \cdot (\mathrm{invFactorial}\left(((((\mathrm{asInt}\left(\mathrm{int}\left(N\right)\right)) - (1)) + (\mathrm{int}\left(k\right))) - (\mathrm{int}\left(i\right))) - (\mathrm{int}\left(j\right))\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.kernelFlux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of kernelFlux.

**Definition 1.26 (racahPrefactor).**

$$\forall N \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{racahPrefactor}\left(N, i, j\right)\right) = ((\mathrm{rat}\left(N\right)) \cdot (\mathrm{deltaSq}\left((2) \cdot (i), (N) - (1), (N) - (1)\right))) \cdot (\mathrm{deltaSq}\left((2) \cdot (j), (N) - (1), (N) - (1)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahPrefactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of racahPrefactor.

**Definition 1.27 (kernelSequence).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathit{Nat},\; \forall i \in \mathit{Nat},\; \mathrm{asRat}\left(\mathrm{kernelSequence}\left(N, j, i\right)\right) = (\mathrm{racahPrefactor}\left(N, i, j\right)) \cdot (\sum_{k\in\mathrm{range}\left((j) + (1)\right)}(\mathrm{factorialKernel}\left(N, i, j, k\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.kernelSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equation is the defining expression of kernelSequence.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.W`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.Wij`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.admissible`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.admissibleDecidable`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.casimir`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.certificateBase`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.certificatePolynomial`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.deltaSq`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.factorialKernel`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.invFactorial`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.kernelFlux`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.kernelSequence`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.lower`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.newtonBasis`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.normalizedRacah`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.polynomial_harmonic`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahCoefficient`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahMonomial`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahPolynomial`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahPrefactor`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahSum`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.racahTerm`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.recurrence_unique`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.sixJ`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.triangle`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.triangleDecidable`
- Truth anchor: `D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.upper`
