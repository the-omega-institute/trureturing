# Pure-qubit affine geometry

## Abstract

A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.

All matrices, vector spaces, predicates and maps below use the indicated Lean and Mathlib objects. Fin m is the outcome index type, and EuclideanSpace over the reals on Fin 3 is the Bloch-vector space. DensityState on Fin 2 is the canonical space of positive trace-one qubit states; Subtype.val exposes its CStarMatrix value. Real scalars enter complex matrices through Complex.ofReal, and WithLp.toLp 2 equips coordinate functions with the Euclidean structure. Division by zero and the real square root use their total real conventions.

The spectral expression specifies the chosen eigenvector unitary and eigenvalues of the positive matrix. Linear maps are determined by their typed underlying functions. The rank-two conclusion uses the coordinate isometry OrthonormalBasis.repr of the chosen basis.

**Definition 1.1 (Spectral SLD information).**

$$\forall n \in Type*,\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall hp \in \operatorname{Matrix.PosSemidef}\left(rho\right),\; \operatorname{let} (U: \operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right)) := (((hp).isHermitian).eigenvectorUnitary); (\operatorname{let} (M: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)) := (\operatorname{star}\left((U: \operatorname{Matrix}\left(n, n, \mathbb{C}\right))\right) \cdot B \cdot (U: \operatorname{Matrix}\left(n, n, \mathbb{C}\right))); (\operatorname{spectralQFI}\left(rho, B, hp\right) = \sum_{(i: n)} (\sum_{(j: n)} (\frac{2 \cdot \operatorname{Complex.normSq}\left(M\left(i, j\right)\right)}{((hp).isHermitian).eigenvalues\left(i\right) + ((hp).isHermitian).eigenvalues\left(j\right)}))))$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral expression uses the chosen Hermitian eigenbasis and assigns zero to terms with zero denominator.

**Definition 1.2 (Guarded real infimum).**

$$\forall S \in \operatorname{Set}\left(\mathbb{R}\right),\; \operatorname{guardedInfimum}\left(S\right) = \operatorname{ite}\left((\operatorname{Set.Nonempty}\left(S\right)) \land (\operatorname{BddBelow}\left(S\right)), \operatorname{sInf}\left(S\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real infimum with explicit nonempty and bounded-below guard.

**Definition 1.3 (Canonical density-state bridge).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall hM \in \operatorname{Matrix.PosSemidef}\left(M\right),\; \forall ht \in \operatorname{Matrix.trace}\left(M\right) = 1,\; ((\operatorname{densityBridge}\left(M, hM, ht\right): \operatorname{Subtype}\left(((rho: \operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right)) \mapsto ((\operatorname{CStarMatrix.ofMatrix}).symm\left(\operatorname{Subtype.val}\left(rho\right)\right) = M))\right)) = \langle\langle\operatorname{CStarMatrix.ofMatrix}\left(M\right), \left(\operatorname{map}_{nonneg}\right)\left(\operatorname{CStarMatrix.ofMatrixStarAlgEquiv}, (hM).nonneg\right), ht\rangle, rfl\rangle) \land ((\operatorname{CStarMatrix.ofMatrix}).symm\left(\operatorname{Subtype.val}\left(\operatorname{Subtype.val}\left(\operatorname{densityBridge}\left(M, hM, ht\right)\right)\right)\right) = M)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bridge constructs the canonical density state represented by the given positive trace-one matrix. Its state value is CStarMatrix.ofMatrix M, its positivity proof is map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg, and its trace proof is ht. The recovered-matrix equality is reflexive.

**Definition 1.4 (Full actual program class).**

$$\forall m \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall R \in \mathbb{R},\; \forall N \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall rho \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall I \in \operatorname{Set}\left(\mathbb{R}\right),\; \forall Q \in \mathbb{R},\; (\operatorname{IsProgram}\left(p, v, R, N, rho, I, Q\right)) \Leftrightarrow ((\operatorname{IsOpen}\left(I\right)) \land ((\operatorname{IsPreconnected}\left(I\right)) \land ((\operatorname{Set.Icc}\left(-(R), R\right) \subseteq I) \land ((\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{Matrix.PosSemidef}\left(N\left(j\right)\right)) \land ((\sum_{(j: \operatorname{Fin}\left(m\right))} (N\left(j\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) \land ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, rho, I\right)) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(rho\left(u\right)\right)) \land ((\operatorname{Matrix.trace}\left(rho\left(u\right)\right) = 1) \land ((rho\left(u\right) \cdot rho\left(u\right) = rho\left(u\right)) \land (\exists r \in \operatorname{FiniteStateChannel.DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; (\operatorname{CStarMatrix.ofMatrix}).symm\left(\operatorname{Subtype.val}\left(r\right)\right) = rho\left(u\right)))))) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow (\forall j \in \operatorname{Fin}\left(m\right),\; (\operatorname{Matrix.trace}\left(N\left(j\right) \cdot rho\left(u\right)\right) = \operatorname{Complex.ofReal}\left(p\left(j\right) + u \cdot v\left(j\right)\right)) \land (0 < p\left(j\right) + u \cdot v\left(j\right)))) \land (\forall h \in \operatorname{Matrix.PosSemidef}\left(rho\left(0\right)\right),\; \operatorname{spectralQFI}\left(rho\left(0\right), \operatorname{deriv}\left(rho, 0\right), h\right) = Q)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate quantifies the full finite measurement and pure-curve data. The interval contains the closed radius interval, and the Born equation is an equality in the complex numbers with the real affine value embedded in them. The final clause quantifies over every proof of positivity at zero, exactly as displayed, even for arbitrary real R.

**Definition 1.5 (Attainable actual costs).**

$$\forall m \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall R \in \mathbb{R},\; \operatorname{costs}\left(p, v, R\right) = \{(Q: \mathbb{R})\mid \exists N \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \exists rho \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \exists I \in \operatorname{Set}\left(\mathbb{R}\right),\; \operatorname{IsProgram}\left(p, v, R, N, rho, I, Q\right)\}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set ranges over all actual programs in the preceding class.

**Definition 1.6 (Cost infimum).**

$$\forall m \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall R \in \mathbb{R},\; \operatorname{C2}\left(p, v, R\right) = \operatorname{guardedInfimum}\left(\operatorname{costs}\left(p, v, R\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C2 applies the guarded infimum to the attainable cost set; when the guard fails its value is zero.

**Definition 1.7 (Bloch vector).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{bloch}\left(M\right) = \operatorname{WithLp.toLp}\left(2, ![2 \cdot \operatorname{Complex.re}\left(M\left(0, 1\right)\right), -(2) \cdot \operatorname{Complex.im}\left(M\left(0, 1\right)\right), \operatorname{Complex.re}\left(M\left(0, 0\right)\right) - \operatorname{Complex.re}\left(M\left(1, 1\right)\right)]\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three real Bloch coordinates of a two by two matrix.

**Definition 1.8 (Bloch matrix).**

$$\forall a \in \mathbb{R},\; \forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{blochMatrix}\left(a, r\right) = \begin{pmatrix}\frac{\operatorname{Complex.ofReal}\left(a + r\left(2\right)\right)}{2}&\frac{\operatorname{Complex.ofReal}\left(r\left(0\right)\right) - \operatorname{Complex.ofReal}\left(r\left(1\right)\right) \cdot \operatorname{Complex.I}}{2}\\\frac{\operatorname{Complex.ofReal}\left(r\left(0\right)\right) + \operatorname{Complex.ofReal}\left(r\left(1\right)\right) \cdot \operatorname{Complex.I}}{2}&\frac{\operatorname{Complex.ofReal}\left(a - r\left(2\right)\right)}{2}\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian matrix with a specified real trace and Bloch vector.

**Theorem 1.9 (Trace of a Bloch matrix).**

$$\forall a \in \mathbb{R},\; \forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.trace}\left(\operatorname{blochMatrix}\left(a, r\right)\right) = \operatorname{Complex.ofReal}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar coordinate is the complex trace, with the real scalar embedded in the complex numbers.

**Theorem 1.10 (Bloch coordinates of a Bloch matrix).**

$$\forall a \in \mathbb{R},\; \forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{bloch}\left(\operatorname{blochMatrix}\left(a, r\right)\right) = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch_blochMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bloch map recovers the vector coordinate for every real scalar and every real three-dimensional vector.

**Theorem 1.11 (Hermitian Bloch geometry).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{Matrix.IsHermitian}\left(M\right)) \Rightarrow ((M = \operatorname{blochMatrix}\left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(M\right)\right), \operatorname{bloch}\left(M\right)\right)) \land ((\operatorname{Matrix.trace}\left(M\right) = 1) \Rightarrow ((M \cdot M = M) \Rightarrow (\left\lVert \operatorname{bloch}\left(M\right) \right\rVert = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch_geometry_of_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hermitian qubit matrix is determined by its trace and Bloch vector. If it has trace one and is idempotent, its Bloch vector has norm one.

**Theorem 1.12 (Positive Bloch norm bound).**

$$\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(M\right)) \Rightarrow (\left\lVert \operatorname{bloch}\left(M\right) \right\rVert \le \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(M\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.norm_bloch_le_trace_of_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite qubit matrix, the Bloch-vector norm is at most the real part of the trace. The determinant equals one quarter of the difference between the squared trace and the squared Bloch norm.

**Definition 1.13 (Visible readout map).**

$$\forall m \in \mathbb{N},\; \forall N \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{DFunLike.coe}\left((\operatorname{effectReadout}\left(N\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{Fin}\left(m\right) \to \mathbb{R}\right))\right) = ((r: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)) \mapsto (((j: \operatorname{Fin}\left(m\right)) \mapsto (\frac{\langle\operatorname{bloch}\left(N\left(j\right)\right), r\rangle_{\mathbb{R}}}{2}))))$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors.

**Definition 1.14 (Orthogonal change of Bloch coordinates).**

$$\forall O \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right),\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{reframe}\left(O, M\right) = \operatorname{blochMatrix}\left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(M\right)\right), O\left(\operatorname{bloch}\left(M\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An orthogonal change of the Bloch vector preserves the trace coordinate.

**Definition 1.15 (Linear Bloch map).**

$$\operatorname{DFunLike.coe}\left((\operatorname{blochLinear}: \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right))\right) = \operatorname{bloch}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch coordinates form a real linear map on complex matrices.

**Definition 1.16 (Linear change of matrix coordinates).**

$$\forall O \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right),\; \operatorname{DFunLike.coe}\left((\operatorname{reframeLinear}\left(O\right): \operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right))\right) = \operatorname{reframe}\left(O\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed orthogonal Bloch frame induces a real linear map on matrices.

**Definition 1.17 (Small quadratic root).**

$$\forall p \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall w \in \mathbb{R},\; \operatorname{root}\left(p, d, alpha, e, w\right) = \frac{2 \cdot \left(1 - e\right) \cdot (w)^{2} \cdot (d)^{2}}{p - alpha \cdot e \cdot w \cdot d + \operatorname{Real.sqrt}\left((p - alpha \cdot e \cdot w \cdot d)^{2} - 4 \cdot e \cdot \left(1 - e\right) \cdot (w)^{2} \cdot (d)^{2}\right)}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores.

**Definition 1.18 (Radius map).**

$$\forall B \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall w \in \mathbb{R} \to \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{radiusMap}\left(B, alpha, w, t\right) = \frac{\left(2 \cdot t \cdot \operatorname{Real.sqrt}\left(1 - (t)^{2}\right) - \left|alpha\right| \cdot (t)^{2}\right) \cdot w\left((t)^{2}\right)}{\left(1 + t\right) \cdot \operatorname{Real.sqrt}\left(B\right)}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This real function converts an arc parameter into a radius for the effect-family statement.

**Definition 1.19 (Extended family cost).**

$$\forall B \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall w \in \mathbb{R} \to \mathbb{R},\; \forall e \in \mathbb{R},\; \operatorname{extendedCost}\left(B, alpha, w, e\right) = \frac{\frac{B}{(w\left(e\right))^{2}} \cdot 4 \cdot \left(1 - e\right)}{4 \cdot \left(1 - e\right) - (alpha)^{2} \cdot e}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost formula extends through the zero transverse parameter for the normalization branch.

**Definition 1.20 (Upper diagonal coefficient).**

$$\forall p \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall w \in \mathbb{R},\; \operatorname{upperDiag}\left(p, d, alpha, e, w\right) = \frac{p - alpha \cdot e \cdot w \cdot d + \operatorname{Real.sqrt}\left((p - alpha \cdot e \cdot w \cdot d)^{2} - 4 \cdot e \cdot \left(1 - e\right) \cdot (w)^{2} \cdot (d)^{2}\right)}{2 \cdot \left(1 - e\right)}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary quadratic root determines the upper diagonal effect coefficient.

**Definition 1.21 (Actual effect matrix).**

$$\forall p \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall w \in \mathbb{R},\; \operatorname{effect}\left(p, d, alpha, e, w\right) = \begin{pmatrix}\operatorname{Complex.ofReal}\left(\operatorname{upperDiag}\left(p, d, alpha, e, w\right)\right)&\operatorname{Complex.ofReal}\left(w \cdot d\right)\\\operatorname{Complex.ofReal}\left(w \cdot d\right)&\operatorname{Complex.ofReal}\left(\operatorname{root}\left(p, d, alpha, e, w\right)\right)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two diagonal coefficients and the normalized direction determine each effect matrix.

**Definition 1.22 (Pure-state arc).**

$$\forall e \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall u \in \mathbb{R},\; \operatorname{arc}\left(e, x, c, u\right) = \operatorname{blochMatrix}\left(1, \operatorname{WithLp.toLp}\left(2, ![x + c \cdot u, \operatorname{Real.sqrt}\left(4 \cdot e \cdot \left(1 - e\right) - (x + c \cdot u)^{2}\right), 1 - 2 \cdot e]\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate.

**Theorem 1.23 (Actual rank-two arc and feasible coefficients).**

$$\forall m \in \mathbb{N},\; \forall N \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall rho \in \mathbb{R} \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall p \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall v \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \forall I \in \operatorname{Set}\left(\mathbb{R}\right),\; ((\operatorname{IsOpen}\left(I\right)) \land ((\operatorname{IsPreconnected}\left(I\right)) \land ((0 \in I) \land ((v \ne 0) \land ((\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{Matrix.PosSemidef}\left(N\left(j\right)\right)) \land ((\sum_{(j: \operatorname{Fin}\left(m\right))} (N\left(j\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) \land ((\operatorname{ContDiffOn}\left(\mathbb{R}, 1, rho, I\right)) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(rho\left(u\right)\right)) \land ((\operatorname{Matrix.trace}\left(rho\left(u\right)\right) = 1) \land (rho\left(u\right) \cdot rho\left(u\right) = rho\left(u\right))))) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow (\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(N\left(j\right) \cdot rho\left(u\right)\right)\right) = p\left(j\right) + u \cdot v\left(j\right))) \land (\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{LinearMap.range}\left(\operatorname{effectReadout}\left(N\right)\right)\right) = 2)))))))))) \Rightarrow (\exists basis \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(3\right), \mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right),\; \exists x \in \mathbb{R},\; \exists c \in \mathbb{R},\; \exists epsilon \in \mathbb{R},\; \exists s \in \mathbb{R},\; \exists A \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \exists q \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; \exists b \in \operatorname{Fin}\left(m\right) \to \mathbb{R},\; (0 < c) \land ((0 < epsilon) \land ((epsilon \le \frac{1}{2}) \land (((s = 1) \lor (s = -(1))) \land ((\forall j \in \operatorname{Fin}\left(m\right),\; (0 \le q\left(j\right)) \land ((0 \le A\left(j\right)) \land (((b\left(j\right))^{2} \le A\left(j\right) \cdot q\left(j\right)) \land ((b\left(j\right) = \frac{v\left(j\right)}{c}) \land (A\left(j\right) = \frac{p\left(j\right) - b\left(j\right) \cdot x - epsilon \cdot q\left(j\right)}{1 - epsilon}))))) \land ((\sum_{(j: \operatorname{Fin}\left(m\right))} (q\left(j\right)) = 1) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow (\operatorname{reframe}\left(\operatorname{OrthonormalBasis.repr}\left(basis\right), rho\left(u\right)\right) = \operatorname{blochMatrix}\left(1, \operatorname{WithLp.toLp}\left(2, ![x + c \cdot u, s \cdot \operatorname{Real.sqrt}\left(4 \cdot epsilon \cdot \left(1 - epsilon\right) - (x + c \cdot u)^{2}\right), 1 - 2 \cdot epsilon]\right)\right))) \land ((\forall u \in \mathbb{R},\; (u \in I) \Rightarrow ((x + c \cdot u)^{2} < 4 \cdot epsilon \cdot \left(1 - epsilon\right))) \land (\forall R \in \mathbb{R},\; (0 \le R) \Rightarrow ((\operatorname{Set.Icc}\left(-(R), R\right) \subseteq I) \Rightarrow (\left|x\right| + c \cdot R < \operatorname{Real.sqrt}\left(4 \cdot epsilon \cdot \left(1 - epsilon\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis supplies a fixed coordinate frame. The coefficients and the signed square-root coordinate satisfy exactly the conjunction below; the last bound holds for every nonnegative radius whose closed interval lies in I.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix_trace`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch_blochMatrix`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch_geometry_of_isHermitian`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.norm_bloch_le_trace_of_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.root`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
