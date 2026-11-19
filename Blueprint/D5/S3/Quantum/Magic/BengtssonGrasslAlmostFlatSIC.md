# The almost flat SIC X-overlap equation

## Abstract

Every almost flat Weyl-Heisenberg SIC fiducial in odd dimension satisfies the X-overlap equation. Finite character orthogonality supplies a diagonal quartic contraction; conjugate reflection and midpoint reindexing reduce its total to a saturated phase bound.

**Definition 1.1 (The almost flat ansatz).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \operatorname{IsAlmostFlat}\left(d, v\right) \Leftrightarrow ((v\left(0\right) = (i) \cdot (\operatorname{sqrt}\left((\operatorname{sqrt}\left((d) + (1)\right)) + (2)\right))) \land (\forall j \in \operatorname{ZMod}\left(d\right),\; (j \ne 0) \Rightarrow ((\left\lVert v\left(j\right) \right\rVert = 1) \land (v\left(-(j)\right) = -(\operatorname{conj}\left(v\left(j\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.IsAlmostFlat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The zeroth coordinate is i times the positive square root of sqrt(d+1)+2. Every other coordinate has modulus one and negative conjugate reflection. No existence assertion is included.

**Definition 1.2 (The normalization denominator).**

$$\forall d \in \mathbb{N},\; \operatorname{almostFlatNorm}\left(d\right) = ((d) + (1)) + (\operatorname{sqrt}\left((d) + (1)\right))$$

*Formalization.* `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.almostFlatNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

This real number is d+1+sqrt(d+1), equal to the Hermitian squared norm of an almost flat vector.

**Theorem 1.3 (The action of every shift power).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall n \in \mathbb{N},\; \forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \forall r \in \operatorname{ZMod}\left(d\right),\; \left(((\operatorname{shiftMatrix}\left(d\right))^{n}) \cdot (v)\right)\left(r\right) = v\left((r) - (n)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.shift_pow_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The circulant convention gives (X to the power n times v) at r equal to v at r-n. Exponents on the left are natural numbers and indices on the right are residues.

**Theorem 1.4 (Weyl overlaps in coordinates).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \forall a \in \operatorname{ZMod}\left(d\right),\; \forall b \in \operatorname{ZMod}\left(d\right),\; \operatorname{inner}\left(v, (\operatorname{displacement}\left(d, a, b\right)) \cdot (v)\right) = \sum_{r : \operatorname{ZMod}\left(d\right)} (((\operatorname{conj}\left(v\left((r) + (a)\right)\right)) \cdot (v\left(r\right))) \cdot (\operatorname{chi}\left((b) \cdot (r)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.displacement_overlap_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The displacement is X to the power a times Z to the power b. The standard positive additive character is denoted chi. Shifting the summation variable removes the translation from the clock factor.

**Theorem 1.5 (Character orthogonality and autocorrelation).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall f \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \forall j \in \operatorname{ZMod}\left(d\right),\; \sum_{b : \operatorname{ZMod}\left(d\right)} ((\operatorname{chi}\left(-((b) \cdot (j))\right)) \cdot ((\operatorname{conj}\left(\sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{chi}\left((b) \cdot (r)\right)) \cdot (f\left(r\right)))\right)) \cdot (\sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{chi}\left((b) \cdot (r)\right)) \cdot (f\left(r\right)))))) = (d) \cdot (\sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{conj}\left(f\left(r\right)\right)) \cdot (f\left((r) + (j)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.spectral_autocorrelation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

Expand a Fourier sum times its conjugate and sum over the character index. Orthogonality retains exactly the terms r=t+j. This identity holds for every complex function on the cyclic index group.

**Theorem 1.6 (The diagonal quartic contraction).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \forall K \in \mathbb{R},\; (\forall a \in \operatorname{ZMod}\left(d\right),\; \forall b \in \operatorname{ZMod}\left(d\right),\; (\left\lVert \operatorname{inner}\left(v, (\operatorname{displacement}\left(d, a, b\right)) \cdot (v)\right) \right\rVert)^{2} = (K) \cdot ((1) + (\operatorname{ite}\left((a = 0) \land (b = 0), d, 0\right)))) \Rightarrow (\forall j \in \operatorname{ZMod}\left(d\right),\; \sum_{r : \operatorname{ZMod}\left(d\right)} ((((\operatorname{conj}\left(v\left((r) + (j)\right)\right))^{2}) \cdot (v\left(r\right))) \cdot (v\left((r) + ((2) \cdot (j))\right))) = \operatorname{ite}\left(j = 0, (2) \cdot (K), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.diagonal_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

Apply spectral autocorrelation to f(r)=conjugate(v(r+j)) v(r). The autocorrelation is the conjugate of the displayed quartic sum. The SIC spectral squares are constant away from the identity, so only j=0 survives, with value 2K.

**Theorem 1.7 (The explicit negative even-shift overlap).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; \forall j \in \operatorname{ZMod}\left(d\right),\; \operatorname{inner}\left(v, ((\operatorname{shiftMatrix}\left(d\right))^{\operatorname{val}\left(-((2) \cdot (j))\right)}) \cdot (v)\right) = \sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{conj}\left(v\left(r\right)\right)) \cdot (v\left((r) + ((2) \cdot (j))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.overlap_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The negative even shift X to the power -2j uses the least nonnegative representative of its residue. Its matrix overlap is exactly the sum of conjugate(v(r)) v(r+2j).

**Theorem 1.8 (Reflection at every coordinate).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow (\forall r \in \operatorname{ZMod}\left(d\right),\; \operatorname{conj}\left(v\left(r\right)\right) = -(v\left(-(r)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.conjugate_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The ansatz reflection extends to zero because the distinguished coordinate is purely imaginary.

**Theorem 1.9 (The squared coordinate norms).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow (\forall r \in \operatorname{ZMod}\left(d\right),\; (\left\lVert v\left(r\right) \right\rVert)^{2} = (1) + (\operatorname{ite}\left(r = 0, (\operatorname{sqrt}\left((d) + (1)\right)) + (1), 0\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.coordinate_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The squared norm is sqrt(d+1)+2 at zero and one elsewhere.

**Theorem 1.10 (The actual squared norm).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow (\operatorname{inner}\left(v, v\right) = \operatorname{almostFlatNorm}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.squared_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

Summing the coordinate squared norms gives the exact normalization denominator.

**Theorem 1.11 (Removing the normalization factor).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow ((\operatorname{IsSICFiducial}\left(d, ((\operatorname{sqrt}\left(\operatorname{almostFlatNorm}\left(d\right)\right))^{-(1)}) \cdot (v)\right)) \Rightarrow (\forall a \in \operatorname{ZMod}\left(d\right),\; \forall b \in \operatorname{ZMod}\left(d\right),\; (\left\lVert \operatorname{inner}\left(v, (\operatorname{displacement}\left(d, a, b\right)) \cdot (v)\right) \right\rVert)^{2} = (((\operatorname{sqrt}\left((d) + (1)\right)) + (1))^{2}) \cdot ((1) + (\operatorname{ite}\left((a = 0) \land (b = 0), d, 0\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.sic_overlap_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

Write s=sqrt(d+1) and C=s+1. The denominator L=sC, so unnormalized nonidentity overlap moduli are C. The identity overlap is L; its square is C squared times d+1.

**Theorem 1.12 (Autocorrelation as negative convolution).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow (\forall j \in \operatorname{ZMod}\left(d\right),\; \sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{conj}\left(v\left(r\right)\right)) \cdot (v\left((r) + ((2) \cdot (j))\right))) = -(\sum_{r : \operatorname{ZMod}\left(d\right)} ((v\left(r\right)) \cdot (v\left(((2) \cdot (j)) - (r)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.overlap_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

Substitute r by -r and use conjugate reflection. This explains the negative sign in the midpoint contraction.

**Theorem 1.13 (Summing over the midpoint).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow (\sum_{j : \operatorname{ZMod}\left(d\right)} (\sum_{r : \operatorname{ZMod}\left(d\right)} ((((\operatorname{conj}\left(v\left((r) + (j)\right)\right))^{2}) \cdot (v\left(r\right))) \cdot (v\left((r) + ((2) \cdot (j))\right)))) = -(\sum_{k : \operatorname{ZMod}\left(d\right)} (((\operatorname{conj}\left(v\left(k\right)\right))^{2}) \cdot (\sum_{r : \operatorname{ZMod}\left(d\right)} ((\operatorname{conj}\left(v\left(r\right)\right)) \cdot (v\left((r) + ((2) \cdot (k))\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.midpoint_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

For each fixed r, replace j by k=r+j, interchange the two finite sums and use the negative convolution identity.

**Theorem 1.14 (A saturated aggregate phase bound).**

$$\forall T \in \operatorname{Type}\left(\right),\; [\operatorname{DecidableEq}\left(T\right)] \forall S \in \operatorname{Finset}\left(T\right),\; \forall z \in (T \to \mathbb{C}),\; \forall A \in (T \to \mathbb{C}),\; \forall C \in \mathbb{R},\; (\forall k \in T,\; (k \in S) \Rightarrow (\left\lVert z\left(k\right) \right\rVert = 1)) \Rightarrow ((\forall k \in T,\; (k \in S) \Rightarrow (\left\lVert A\left(k\right) \right\rVert = C)) \Rightarrow ((\sum_{k \in S} (((\operatorname{conj}\left(z\left(k\right)\right))^{2}) \cdot (A\left(k\right))) = (C) \cdot (\operatorname{card}\left(S\right))) \Rightarrow (\forall k \in T,\; (k \in S) \Rightarrow (A\left(k\right) = (C) \cdot ((z\left(k\right))^{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.phase_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

For a finite index set S, each z has modulus one and each A has modulus C. Expanding the sum of norm squares of A-C z squared gives zero when the aggregate conjugate phase sum is C times the cardinality. Nonnegativity forces every error to vanish.

**Theorem 1.15 (The X-overlap equation in every odd dimension).**

$$\forall d \in \mathbb{N},\; (d \ne 0) \Rightarrow ((\operatorname{Odd}\left(d\right)) \Rightarrow (\forall v \in (\operatorname{ZMod}\left(d\right) \to \mathbb{C}),\; (\operatorname{IsAlmostFlat}\left(d, v\right)) \Rightarrow ((\operatorname{IsSICFiducial}\left(d, ((\operatorname{sqrt}\left(\operatorname{almostFlatNorm}\left(d\right)\right))^{-(1)}) \cdot (v)\right)) \Rightarrow (\forall j \in \operatorname{ZMod}\left(d\right),\; (j \ne 0) \Rightarrow (\operatorname{inner}\left(v, ((\operatorname{shiftMatrix}\left(d\right))^{\operatorname{val}\left(-((2) \cdot (j))\right)}) \cdot (v)\right) = ((\operatorname{sqrt}\left((d) + (1)\right)) + (1)) \cdot ((v\left(j\right))^{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.result` (`✓ std3`). ∎

*Resolves.* `Problems/bengtsson-grassl-2025-almost-flat-sic-conjecture` (proved) by `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bengtsson-grassl-2025-almost-flat-sic-conjecture","declaration_gid":"D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ingemar Bengtsson; Markus Grassl (2025). *A Conjecture on Almost Flat SIC-POVMs*. URL: <https://arxiv.org/abs/2512.13201>.

*Commentary.*

The diagonal quartic contraction sums to 2C squared. The zero term is conjugate(v(0)) squared times A(0)=-(s+2)L; removing it from the total -2C squared leaves C(d-1). Oddness makes multiplication by two invertible, so every remaining even shift is nonidentity and its overlap modulus is C. Phase saturation gives A(j)=C v(j) squared for every nonzero j. Dimension one has no such j. The theorem is conditional on a SIC fiducial and does not assert existence in any dimension. It does not address the converse, the even-dimensional formulas or alternative Weyl phase conventions.

## References

- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.IsAlmostFlat`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.almostFlatNorm`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.conjugate_reflection`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.coordinate_norm_sq`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.diagonal_quartic`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.displacement_overlap_sum`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.midpoint_contraction`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.overlap_convolution`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.overlap_sum`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.phase_saturation`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.result`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.shift_pow_mulVec`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.sic_overlap_squares`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.spectral_autocorrelation`
- Truth anchor: `D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC.squared_norm`
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation](ErewGoldsteinSICStabilizerRefutation.md)
- Dependency: [D5/S3/Quantum/Magic/ParitySectorMoments](ParitySectorMoments.md)
