# Clifford transformations can change the autocorrelation operator norm

## Abstract

In dimension five, a Fourier Clifford changes the Euclidean operator norm of the matrix of cyclic MUB probability autocorrelations.

All indices in Fin(5) are residues modulo five, represented by 0, 1, 2, 3 and 4; val takes the corresponding natural-number representative. The six basis labels are Option(Fin(5)): ∞ denotes none, and some(m) is the finite label m. Write ω, τ, X, Z, D, P, p, A, F and ψ for omega, tau, shift, clock, displacement, projector, probability, autocorr, fourier and psi, respectively. I is the imaginary unit; a star on a matrix denotes conjugate transpose. Matrix norms with subscript op are induced by the Euclidean norms on both index spaces.

**Definition 1.1 (The fifth root of unity).**

$$\omega = \operatorname{exp}\left(\frac{((2) \cdot (\pi)) \cdot (\operatorname{I})}{5}\right)$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.omega` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

The standard positive fifth root is exp(2πI/5). This is the Weyl–Heisenberg root used in Section I.

**Definition 1.2 (The displacement phase).**

$$\tau = (\omega)^{3}$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.tau` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

In dimension five, the standard phase −exp(πI/5) equals ω cubed.

**Definition 1.3 (The cyclic shift).**

$$X = (\lambda (i: \operatorname{Fin}\left(5\right)) \mapsto ((\lambda (j: \operatorname{Fin}\left(5\right)) \mapsto ((\operatorname{if} (i = j + 1) \operatorname{then} (1) \operatorname{else} (0))))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.shift` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

The shift sends the computational vector at j to the vector at j + 1. Addition is in Fin(5).

**Definition 1.4 (The clock matrix).**

$$Z = \operatorname{diagonal}\left((\lambda (j: \operatorname{Fin}\left(5\right)) \mapsto ((\omega)^{\operatorname{val}\left(j\right)}))\right)$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.clock` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

The clock is diagonal, with entry ω to the power val(j) at j. Together X and Z are the standard Weyl generators.

**Definition 1.5 (Weyl–Heisenberg displacements).**

$$\forall (p: \operatorname{Fin}\left(5\right)), (\forall (q: \operatorname{Fin}\left(5\right)), (\operatorname{D}\left(p, q\right) = ((\tau)^{(\operatorname{val}\left(p\right)) \cdot (\operatorname{val}\left(q\right))}) \cdot (((X)^{\operatorname{val}\left(p\right)}) \cdot ((Z)^{\operatorname{val}\left(q\right)}))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.displacement` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

The phase exponent uses the product of the natural representatives of p and q. Scalar multiplication is denoted by a centered dot; the two matrix powers are multiplied in the order X then Z.

**Definition 1.6 (The six MUB projector families).**

$$(\forall (j: \operatorname{Fin}\left(5\right)), (\operatorname{P}\left(\infty, j\right) = (\frac{1}{5}) \cdot (\sum_{r: \operatorname{Fin}\left(5\right)} (((\omega)^{\operatorname{val}\left((-j) \cdot (r)\right)}) \cdot (\operatorname{D}\left(r, 0\right)))))) \land (\forall (m: \operatorname{Fin}\left(5\right)), (\forall (j: \operatorname{Fin}\left(5\right)), (\operatorname{P}\left(\operatorname{some}\left(m\right), j\right) = (\frac{1}{5}) \cdot (\sum_{r: \operatorname{Fin}\left(5\right)} (((\omega)^{\operatorname{val}\left((-j) \cdot (r)\right)}) \cdot (\operatorname{D}\left((m) \cdot (r), r\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.projector` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

These are the standard spectral projectors of the Weyl lines. The infinite line uses D(r,0), and the finite line m uses D(mr,r). The product −jr is taken modulo five before val supplies the exponent; the finite-line product mr is also in Fin(5). Each sum runs over all five residues.

**Definition 1.7 (Born probabilities).**

$$\forall (v: (\operatorname{Fin}\left(5\right) \to \mathbb{C})), (\forall (m: \operatorname{Option}\left(\operatorname{Fin}\left(5\right)\right)), (\forall (j: \operatorname{Fin}\left(5\right)), (\operatorname{p}\left(v, m, j\right) = \Re\left(\operatorname{dotProduct}\left(\operatorname{star}\left(v\right), \operatorname{mulVec}\left(\operatorname{P}\left(m, j\right), v\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.probability` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Section III uses the probability of outcome j in basis m. Here it is the real part of the expectation of P(m,j). The star on a vector conjugates each coordinate, and dotProduct is the bilinear sum of coordinate products. The definition is given for every complex vector; normalization is imposed in claim.

**Definition 1.8 (The rectangular autocorrelation matrix).**

$$\forall (v: (\operatorname{Fin}\left(5\right) \to \mathbb{C})), (\operatorname{A}\left(v\right) = (\lambda (m: \operatorname{Option}\left(\operatorname{Fin}\left(5\right)\right)) \mapsto ((\lambda (k: \operatorname{Fin}\left(5\right)) \mapsto (\sum_{j: \operatorname{Fin}\left(5\right)} ((\operatorname{p}\left(v, m, j\right)) \cdot (\operatorname{p}\left(v, m, j + k\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.autocorr` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Section III defines A by the cyclic autocorrelation of each MUB probability vector. It is a real matrix with six rows and five columns. The outcome j + k is computed modulo five.

**Definition 1.9 (The Clifford condition).**

$$\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right), \mathbb{C}\right)), (\operatorname{IsClifford}\left(U\right) \Leftrightarrow ((((U)^{*}) \cdot (U) = 1) \land (((U) \cdot ((U)^{*}) = 1) \land ((\exists (p: \operatorname{Fin}\left(5\right)), (\exists (q: \operatorname{Fin}\left(5\right)), (\exists (z: \mathbb{C}), ((\left\lVert z \right\rVert = 1) \land (((U) \cdot (X)) \cdot ((U)^{*}) = (z) \cdot (\operatorname{D}\left(p, q\right))))))) \land (\exists (p: \operatorname{Fin}\left(5\right)), (\exists (q: \operatorname{Fin}\left(5\right)), (\exists (z: \mathbb{C}), ((\left\lVert z \right\rVert = 1) \land (((U) \cdot (Z)) \cdot ((U)^{*}) = (z) \cdot (\operatorname{D}\left(p, q\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.IsClifford` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

The matrix is unitary on both sides and conjugates each Weyl generator to a displacement times a unit-modulus phase. The displacement labels and phase may differ for X and Z. This is the standard normalizer condition on the two generators.

**Definition 1.10 (Clifford invariance of the Euclidean operator norm).**

$$\operatorname{claim} \Leftrightarrow (\forall (v: (\operatorname{Fin}\left(5\right) \to \mathbb{C})), ((\sum_{i: \operatorname{Fin}\left(5\right)} (\operatorname{normSq}\left(v\left(i\right)\right)) = 1) \Rightarrow (\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right), \mathbb{C}\right)), ((\operatorname{IsClifford}\left(U\right)) \Rightarrow (\left\lVert \operatorname{A}\left(\operatorname{mulVec}\left(U, v\right)\right) \right\rVert_{\operatorname{op}} = \left\lVert \operatorname{A}\left(v\right) \right\rVert_{\operatorname{op}})))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.claim` (`✓ std3`).

*Citation.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Section III asserts that Clifford action permutes the rows and columns of A and hence preserves every unitarily invariant norm. The proposition here is its Euclidean operator-norm consequence in dimension five. It quantifies over every vector whose squared complex moduli sum to one and every matrix satisfying IsClifford. The function normSq is the squared complex modulus.

**Definition 1.11 (The Fourier matrix).**

$$F = (\lambda (i: \operatorname{Fin}\left(5\right)) \mapsto ((\lambda (j: \operatorname{Fin}\left(5\right)) \mapsto (\frac{(\omega)^{\operatorname{val}\left((i) \cdot (j)\right)}}{(\sqrt{5}: \mathbb{C})}))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.fourier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Choose the positive-exponent Fourier matrix. Its row and column labels multiply modulo five before val is taken; the denominator is the positive real square root, regarded as a complex number.

**Definition 1.12 (A two-coordinate unit vector).**

$$\psi = (\lambda (j: \operatorname{Fin}\left(5\right)) \mapsto ((\operatorname{if} ((j = 0) \lor (j = 1)) \operatorname{then} (((\sqrt{2}: \mathbb{C}))^{-1}) \operatorname{else} (0))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Choose ψ = (1,1,0,0,0)/√2 in computational order. Its squared moduli sum to one.

**Theorem 1.13 (The operator norm changes under a Fourier Clifford).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/stacey-2025-autocorrelation-norm-clifford-invariance-refutation` (refuted) by `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"stacey-2025-autocorrelation-norm-clifford-invariance-refutation","declaration_gid":"D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Blake C. Stacey (2025). *SICs, the Stabilizer Polytope and Majorization*. URL: <https://arxiv.org/abs/2509.16819v1>.

*Commentary.*

Let W have entries stdAddChar(ji) for residues i,j modulo five. The identity WW* = 5I and F = W/√5 give F*F = FF* = 1. The entry relations FX = ZF and FZ = D(4,0)F then give FXF* = D(0,1) = Z, and FZF* = D(4,0) = X to the fourth power. Both phases are one, so F satisfies IsClifford. Its action on the chosen unit vector has coordinate (1 + ω to the power val(i))/√10 at i.

For the exact probability tables, put a = (3 − √5)/20 and b = (3 + √5)/20, and list outcomes in the order 0,1,2,3,4. For ψ, the rows at ∞,0,1,2,3,4 are respectively (2/5,b,a,a,b), (1/2,1/2,0,0,0), (a,a,b,2/5,b), (b,b,a,2/5,a), (b,b,a,2/5,a), (a,a,b,2/5,b). For Fψ, the rows in the same order are (1/2,0,0,0,1/2), (2/5,b,a,a,b), (a,b,2/5,b,a), (b,a,a,b,2/5), (b,2/5,b,a,a), (a,a,b,2/5,b). These values follow by expanding the displacement entries and the fifth roots of unity.

Taking cyclic autocorrelations gives the rows R = (1/2,1/4,0,0,1/4), S = (3/10,(7 + √5)/40,(7 − √5)/40,(7 − √5)/40,(7 + √5)/40), and T = (3/10,(7 − √5)/40,(7 + √5)/40,(7 + √5)/40,(7 − √5)/40). The rows of A(ψ) are S,R,S,T,T,S, while those of A(Fψ) are R,S,S,S,S,S.

The squared Frobenius norm of A(ψ)*A(ψ) is (2961 + 19√5)/1600. The operator norm is bounded by the Frobenius norm, so the fourth power of the operator norm of A(ψ) is at most this value and its square is less than 7/5. Use S as a test vector for A(Fψ). Its squared Euclidean norm is 9/40, and its image has squared norm (993 + 19√5)/3200. Thus the squared operator norm of A(Fψ) is at least (993 + 19√5)/720, which exceeds 7/5. The two operator norms differ. Applying claim to ψ and F would equate them, proving its negation. In particular, the change of cyclic-difference labels cannot always be expressed by a single common column permutation.

## References

- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.IsClifford`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.autocorr`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.clock`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.displacement`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.fourier`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.omega`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.probability`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.projector`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.psi`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.shift`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerAutocorrelationNormRefutation.tau`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2](../../Arith/Lattices/Klartag/Walk/StepInputs2.md)
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap](../Magic/CepollaroPowerOfTwoZeroMagicGap.md)
- Dependency: [D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry](../Magic/QuquintWignerCriticalGeometry.md)
- Dependency: [D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation](../Measurement/FourierLDOILOCCRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../QuantumChannels/TomiyamaDiagonalKPositivity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample](../QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.md)
