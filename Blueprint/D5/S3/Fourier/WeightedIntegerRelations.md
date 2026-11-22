# Weighted integer-character bounds

## Abstract

Integer relations impose a weighted deficit on finite sine sums.

Let C and R be finite sets of column and row indices in arbitrary types J and A. A phase vector takes values in Circle, the complex numbers of modulus one. Products of integer powers are taken in Circle and their differences and norms are taken in the complex numbers. The notation χ(C,z,k) denotes the character given by the product of z(j) raised to k(j) over j in C.

**Theorem 1.1 (Chord bound for one character).**

$$\forall J \in \mathit{Type},\; \forall C \in \operatorname{Finset}\left(J\right),\; \forall z \in J \to \mathit{Circle},\; \forall q \in J \to \mathit{Circle},\; \forall k \in J \to \mathbb{Z},\; \left\lVert \operatorname{chi}\left(C, z, k\right) - \operatorname{chi}\left(C, q, k\right) \right\rVert \le \sum_{j\in C} \left|\operatorname{k}\left(j\right)\right| \cdot \left\lVert \operatorname{z}\left(j\right) - \operatorname{q}\left(j\right) \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedIntegerRelations.chord_prod_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chord of two products is bounded by the sum of the factor chords because multiplication by a unit complex number preserves norm. Nonnegative powers have chord bounded by the power times the original chord. Inversion on Circle is complex conjugation, so the bound for negative powers has the absolute integer exponent. `D5/S3/AnalyticClosure/ComplexPowerDifference`

**Theorem 1.2 (Simultaneous weighted character chords).**

$$\forall J \in \mathit{Type},\; \forall A \in \mathit{Type},\; \forall C \in \operatorname{Finset}\left(J\right),\; \forall R \in \operatorname{Finset}\left(A\right),\; \forall z \in J \to \mathit{Circle},\; \forall q \in J \to \mathit{Circle},\; \forall w \in J \to \mathbb{R},\; \forall k \in A \to \left(J \to \mathbb{Z}\right),\; \forall lambda \in A \to \mathbb{R},\; \left(\forall j \in J,\; j \in C \Rightarrow 0 < \operatorname{w}\left(j\right)\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow 0 \le \operatorname{lambda}\left(a\right)\right) \Rightarrow (\sum_{a\in R} \operatorname{lambda}\left(a\right) \cdot \left\lVert \operatorname{chi}\left(C, z, \operatorname{k}\left(a\right)\right) - \operatorname{chi}\left(C, q, \operatorname{k}\left(a\right)\right) \right\rVert)^{2} \le (\sum_{j\in C} \frac{(\sum_{a\in R} \operatorname{lambda}\left(a\right) \cdot \left|\operatorname{k}\left(a, j\right)\right|)^{2}}{\operatorname{w}\left(j\right)}) \cdot (\sum_{j\in C} \operatorname{w}\left(j\right) \cdot \left\lVert \operatorname{z}\left(j\right) - \operatorname{q}\left(j\right) \right\rVert^{2})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedIntegerRelations.weighted_character_chord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write kₐ for the integer vector in row a. Sum the chord bounds with nonnegative multipliers λ(a) and collect all the terms from each column. Weighted Cauchy–Schwarz gives the square bound, including overlaps through the column sums taken before squaring.

For real frequencies γ and weights w positive on C, write W(C,w) for the sum of w(j) over C. At each real v let S(v) be the sum of w(j) sin(γ(j)v) over C. For positive W(C,w), D(C,γ,w) is 1 − sup over real v of S(v) divided by W(C,w). Each relation row has zero frequency sum with integer coefficients k(a,j), and δ(C,kₐ) is the norm of the difference between 1 and the power of i whose exponent is the sum of the row's integer coefficients.

**Theorem 1.3 (Phase deficit from nonnegative multipliers).**

$$\forall J \in \mathit{Type},\; \forall A \in \mathit{Type},\; \forall C \in \operatorname{Finset}\left(J\right),\; \forall R \in \operatorname{Finset}\left(A\right),\; \forall gamma \in J \to \mathbb{R},\; \forall w \in J \to \mathbb{R},\; \forall k \in A \to \left(J \to \mathbb{Z}\right),\; \forall lambda \in A \to \mathbb{R},\; \left(\forall j \in J,\; j \in C \Rightarrow 0 < \operatorname{w}\left(j\right)\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow 0 \le \operatorname{lambda}\left(a\right)\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow \sum_{j\in C} \operatorname{k}\left(a, j\right) \cdot \operatorname{gamma}\left(j\right) = 0\right) \Rightarrow \left(0 < \operatorname{W}\left(C, w\right) \Rightarrow \left(0 < \sum_{j\in C} \frac{(\sum_{a\in R} \operatorname{lambda}\left(a\right) \cdot \left|\operatorname{k}\left(a, j\right)\right|)^{2}}{\operatorname{w}\left(j\right)} \Rightarrow \frac{(\sum_{a\in R} \operatorname{lambda}\left(a\right) \cdot \operatorname{delta}\left(C, \operatorname{k}\left(a\right)\right))^{2}}{2 \cdot \operatorname{W}\left(C, w\right) \cdot (\sum_{j\in C} \frac{(\sum_{a\in R} \operatorname{lambda}\left(a\right) \cdot \left|\operatorname{k}\left(a, j\right)\right|)^{2}}{\operatorname{w}\left(j\right)})} \le \operatorname{D}\left(C, \mathit{gamma}, w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedIntegerRelations.weighted_phase_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the orbit exp(iγ(j)v), each relation character is one. At the constant quarter phase i, its value is i raised to the coefficient sum. The weighted sum of squared coordinate chords to i is exactly 2(W − S(v)). The character estimate bounds S(v) uniformly in v, so its supremum satisfies the same upper bound. The multiplier inequality uses positive total mass and positive column energy.

**Theorem 1.4 (Additive deficit for disjoint nonzero rows).**

$$\forall J \in \mathit{Type},\; \forall A \in \mathit{Type},\; \forall C \in \operatorname{Finset}\left(J\right),\; \forall R \in \operatorname{Finset}\left(A\right),\; \forall gamma \in J \to \mathbb{R},\; \forall w \in J \to \mathbb{R},\; \forall k \in A \to \left(J \to \mathbb{Z}\right),\; \left(\forall j \in J,\; j \in C \Rightarrow 0 < \operatorname{w}\left(j\right)\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow \sum_{j\in C} \operatorname{k}\left(a, j\right) \cdot \operatorname{gamma}\left(j\right) = 0\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow \left(\exists j \in J,\; j \in C \land \operatorname{k}\left(a, j\right) \ne 0\right)\right) \Rightarrow \left(\left(\forall a \in A,\; a \in R \Rightarrow \left(\forall b \in A,\; b \in R \Rightarrow \left(a \ne b \Rightarrow \left(\forall j \in J,\; j \in C \Rightarrow \left(\operatorname{k}\left(a, j\right) = 0 \lor \operatorname{k}\left(b, j\right) = 0\right)\right)\right)\right)\right) \Rightarrow \left(0 < \operatorname{W}\left(C, w\right) \Rightarrow \frac{1}{2 \cdot \operatorname{W}\left(C, w\right)} \cdot (\sum_{a\in R} \frac{\operatorname{delta}\left(C, \operatorname{k}\left(a\right)\right)^{2}}{\sum_{j\in C} \frac{\operatorname{k}\left(a, j\right)^{2}}{\operatorname{w}\left(j\right)}}) \le \operatorname{D}\left(C, \mathit{gamma}, w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/WeightedIntegerRelations.weighted_phase_deficit_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero row has positive energy, defined as the sum over j in C of k(a,j)²/w(j). Use the multiplier δ divided by that energy in each row. Disjoint supports eliminate all cross terms from each squared column load. This makes both the numerator before squaring and the column energy equal to the sum of squared defects divided by row energies. When that sum is zero, including an empty row family, the bound follows from S(v) ≤ W.

## References

- Truth anchor: `D5/S3/Fourier/WeightedIntegerRelations.chord_prod_zpow`
- Truth anchor: `D5/S3/Fourier/WeightedIntegerRelations.weighted_character_chord`
- Truth anchor: `D5/S3/Fourier/WeightedIntegerRelations.weighted_phase_deficit`
- Truth anchor: `D5/S3/Fourier/WeightedIntegerRelations.weighted_phase_deficit_disjoint`
- Dependency: [D5/S3/AnalyticClosure/ComplexPowerDifference](../AnalyticClosure/ComplexPowerDifference.md)
- Narrative reference: [D5/S3/AnalyticClosure/ComplexPowerDifference](../AnalyticClosure/ComplexPowerDifference.md)
