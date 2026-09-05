# Universal Replacement Capacity Growth

## Abstract

Universal replacement extracts an orthonormal purification family and forces inner capacity growth.

**Definition 1.1 (Universal single-step replacement).**

$$\begin{aligned}\forall A, B, R: Type,\\\operatorname{Fintype}\left(A\right), \operatorname{DecidableEq}\left(A\right), \operatorname{Fintype}\left(B\right), \operatorname{Fintype}\left(R\right), \operatorname{DecidableEq}\left(R\right),\\\forall W: \operatorname{Matrix}\left(B \times R, A, \mathbb{C}\right), tau: \operatorname{DensityState}\left(R\right),\\\operatorname{UniversalReplacement}\left(W, tau\right) := (\forall rho \in \operatorname{DensityState}\left(A\right),\; \operatorname{partialTraceFirst}\left(((W \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)) \cdot \operatorname{conjTranspose}\left(W\right))\right) = \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(tau\right)\right)).\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.UniversalReplacement` (`✓ std3`).

*Citation.* Samuel L. Braunstein and Arun K. Pati (2007). *Quantum Information Cannot Be Completely Hidden in Correlations: Implications for the Black-Hole Information Paradox*. DOI: [10.1103/PhysRevLett.98.080502](https://doi.org/10.1103/PhysRevLett.98.080502).

*Commentary.*

A, B, and R index the previous inner space, next inner space, and emitted space. The product B times R is the finite coordinate realization of their tensor product. DensityState is the existing positive trace-one CStarMatrix subtype. The displayed CStarMatrix.ofMatrix.symm(val(rho)) is exactly CStarMatrix.ofMatrix.symm rho.val, and conjTranspose is the adjoint. This is equation 55.2: the quantifier ranges over every density input, including coherent superpositions, not only the input basis states.

**Theorem 1.2 (Orthonormal extraction and inner capacity).**

$$\begin{aligned}\forall A, B, R: Type,\\\operatorname{Fintype}\left(A\right), \operatorname{DecidableEq}\left(A\right), \operatorname{Fintype}\left(B\right), \operatorname{Fintype}\left(R\right), \operatorname{DecidableEq}\left(R\right),\\\forall W: \operatorname{Matrix}\left(B \times R, A, \mathbb{C}\right), tau: \operatorname{DensityState}\left(R\right),\\\operatorname{UniversalReplacement}\left(W, tau\right) \implies \\\operatorname{let} M := \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(tau\right)\right),\\\operatorname{let} E := \operatorname{eigenvectorBasis}\left(M\right), lam := \operatorname{eigenvalues}\left(M\right),\\\operatorname{let} S := \{a: R \mid lam\left(a\right) \neq 0\},\\\operatorname{let} v: A \times S \to \operatorname{EuclideanSpace}\left(\mathbb{C}, B\right) := \\ia \mapsto \operatorname{smul}\left(\operatorname{inv}\left(\operatorname{ofReal}\left(\operatorname{sqrt}\left(lam\left(\operatorname{val}\left(\operatorname{snd}\left(ia\right)\right)\right)\right)\right)\right), \operatorname{toLp}\left(2, b \mapsto \sum_{r \in R} \operatorname{star}\left(E\left(\operatorname{val}\left(\operatorname{snd}\left(ia\right)\right), r\right)\right) \cdot W\left((b, r), \operatorname{fst}\left(ia\right)\right)\right)\right),\\(\operatorname{Orthonormal}\left(\mathbb{C}, v\right)) \land (\operatorname{card}\left(A\right) \cdot \operatorname{rank}\left(M\right) \le \operatorname{card}\left(B\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.universal_replacement_capacity_growth` (`✓ std3`). ∎

*Citation.* Samuel L. Braunstein and Arun K. Pati (2007). *Quantum Information Cannot Be Completely Hidden in Correlations: Implications for the Black-Hole Information Paradox*. DOI: [10.1103/PhysRevLett.98.080502](https://doi.org/10.1103/PhysRevLett.98.080502).

*Commentary.*

M and S abbreviate the underlying matrix of tau and its nonzero spectral support. The Lean let hPos transports tau.property.1 through CStarMatrix.ofMatrixStarAlgEquiv.symm and Matrix.nonneg_iff_posSemidef.mp. E and lam are exactly hPos.isHermitian.eigenvectorBasis and eigenvalues. Positivity makes every nonzero eigenvalue positive. No spectral or orthogonality hypothesis is added.

In v, fst and snd are the product projections, val removes the support subtype, ofReal casts Real.sqrt into Complex, inv is complex inverse, and smul is complex scalar multiplication. toLp(2, f) is WithLp.toLp 2 f, giving the EuclideanSpace vector. The sum is over all r in R. Thus v is exactly the inverse-square-root normalized contraction of a column of W against the corresponding emitted eigenvector.

Universal replacement on normalized pure inputs first determines the diagonal contraction pairing. Complex polarization, including imaginary-phase superpositions, then gives the cross-input Gram identity. Orthonormality is derived from this identity. The final count binds Mathlib's orthonormal linear independence and finite dimension bound; matrix rank is the number of nonzero eigenvalues.

The theorem is the exact finite-dimensional no-hiding capacity bound of quantum-reality Theorem 55.2, together with its explicit witness. Equation 55.2 alone is sufficient, so no redundant isometry premise is assumed. This does not assert a result about approximate replacement, small corrections, or arbitrary black-hole models.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.UniversalReplacement`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalReplacementCapacityGrowth.universal_replacement_capacity_growth`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
