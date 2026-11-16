# FourQubitParentConstruction

## Abstract

FourQubitParentConstruction: exact analytic statements for four-qubit white-noise compatibility.

**Definition 1.1 (Compatible4).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \operatorname{Compatible4}\left(E\right) = \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPOVM}\left(E\left(i\right)\right)\right) \land \left(\exists J \in \left(\operatorname{Fin}\left(4\right) \to Bool\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsPOVM}\left(J\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; E\left(i, b\right) = \sum_{(e: \operatorname{Fin}\left(4\right) \to Bool), e\left(i\right) = b} J\left(e\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.Compatible4` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.13 (p. 12): “Let g ∈ ℕ, d ∈ ℕ, and kₓ ∈ ℕ for all x ∈ [g]. Let (Eᵢ∣ₓ)ᵢ∈[kₓ], x ∈ [g] be a collection of g d-dimensional POVMs. These measurements are compatible if there exists another d-dimensional POVM (Jᵢ₁,…,ᵢg)ᵢ₁∈[k₁],…,ᵢg∈[kg] such that” the marginal equality holds. Here g = 4, d = 2 and each outcome set is Bool. The sixteen functions Fin 4 → Bool index the joint outcomes; true denotes the positive sign.

**Definition 1.2 (noisy).**

$$\forall s \in \mathbb{R},\; \forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; \operatorname{noisy}\left(s, E, i, b\right) = (s) \cdot (E\left(i, b\right)) + (1 - s) \cdot (((\frac{1}{2}: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.noisy` (`✓ std3`).

*Citation.* A. Bluhm, E. Evert, I. Klep, V. Magron, I. Nechita (2025). *Inclusion constants for free spectrahedra with applications to quantum incompatibility*. DOI: [10.48550/arXiv.2512.17706](https://doi.org/10.48550/arXiv.2512.17706). URL: <https://arxiv.org/abs/2512.17706v1>.

*Commentary.*

Definition 2.15 (p. 13): “Let k ∈ ℕ and let (Eᵢ)ᵢ∈[k] be a POVM. Let s ∈ [0, 1] be a noise parameter. Then, we define the POVM (Eᵢ(s))ᵢ∈[k] with” Eᵢ(s) := sEᵢ + (1 − s)I/k “as the noisy version of (Eᵢ)ᵢ∈[k].” Here k = 2 and real scalars act on complex matrices.

**Definition 1.3 (endpoint).**

$$(endpoint: \mathbb{R}) = \frac{2}{\sqrt{13}}$$

*Formalization.* `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sharp retained-signal parameter is 2/√13.

**Theorem 1.4 (B_formula).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(a\right) = \begin{pmatrix}(a\left(2\right): \mathbb{C})&(a\left(0\right): \mathbb{C}) - \operatorname{Complex.I} \cdot (a\left(1\right): \mathbb{C})\\(a\left(0\right): \mathbb{C}) + \operatorname{Complex.I} \cdot (a\left(1\right): \mathbb{C})&-(a\left(2\right): \mathbb{C})\end{pmatrix}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pauli expansion gives these four complex matrix entries.

**Theorem 1.5 (B_zero).**

$$\operatorname{B}\left((0: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right))\right) = (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero Bloch vector gives the zero matrix.

**Theorem 1.6 (B_real_smul).**

$$\forall c \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left((c) \cdot (a)\right) = (c) \cdot (\operatorname{B}\left(a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_real_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bloch matrix is homogeneous for the real scalar action.

**Theorem 1.7 (B_neg).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(-a\right) = -\operatorname{B}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating the vector negates its Bloch matrix.

**Theorem 1.8 (B_sum).**

$$\forall U \in Type,\; \forall s \in \operatorname{Finset}\left(U\right),\; \forall a \in U \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{B}\left(\sum_{i \in s} a\left(i\right)\right) = \sum_{i \in s} \operatorname{B}\left(a\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Bloch expansion commutes with finite sums.

**Theorem 1.9 (norm_sq_coords).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \left\lVert a \right\rVert^{2} = a\left(0\right)^{2} + a\left(1\right)^{2} + a\left(2\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.norm_sq_coords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared Euclidean norm is the sum of the three coordinate squares.

**Theorem 1.10 (trace_B_mul).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall b \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.trace}\left(\operatorname{B}\left(a\right) \cdot \operatorname{B}\left(b\right)\right) = (2 \cdot \operatorname{inner}\left(\mathbb{R}, a, b\right): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.trace_B_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace pairing of Bloch matrices is twice the real inner product.

**Theorem 1.11 (scalarB_sum).**

$$\forall U \in Type,\; \forall s \in \operatorname{Finset}\left(U\right),\; \forall t \in U \to \mathbb{R},\; \forall a \in U \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{scalarB}\left(\sum_{j \in s} t\left(j\right), \sum_{j \in s} a\left(j\right)\right) = \sum_{j \in s} \operatorname{scalarB}\left(t\left(j\right), a\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scalar and Bloch coordinates commute with finite sums.

**Theorem 1.12 (scalarB_hermitian).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.IsHermitian}\left(\operatorname{scalarB}\left(t, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real scalar and Bloch coordinates define a Hermitian matrix.

**Theorem 1.13 (hermitian_decomposition).**

$$\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{Matrix.IsHermitian}\left(A\right) \Rightarrow A = \operatorname{scalarB}\left(\frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(A\right)\right)}{2}, ((\frac{1}{2}: \mathbb{R})) \cdot (\operatorname{bloch}\left(A\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.hermitian_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Hermitian two by two matrix is reconstructed from its real trace and Bloch coordinates.

**Theorem 1.14 (half_scalarB_double).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(2 \cdot t, ((2: \mathbb{R})) \cdot (a)\right)) = \operatorname{scalarB}\left(t, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Doubling both coordinates and multiplying the matrix by one half gives the original matrix.

**Theorem 1.15 (half_scalarB_complement).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(2 - t, -a\right)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) - ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(t, a\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complementary effect negates the Bloch vector and replaces the scalar by two minus that scalar.

**Theorem 1.16 (scalarB_posSemidef_iff).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{scalarB}\left(t, a\right)\right) \Leftrightarrow \left\lVert a \right\rVert \le t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant and diagonal entries give the necessary bound. At the boundary, the square identity expresses the matrix as a positive multiple of its conjugate-transpose square; adding a nonnegative scalar identity yields sufficiency.

**Theorem 1.17 (half_scalarB_posSemidef_iff).**

$$\forall t \in \mathbb{R},\; \forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \operatorname{Matrix.PosSemidef}\left(((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(t, a\right))\right) \Leftrightarrow \left\lVert a \right\rVert \le t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the positive scalar 1/2 preserves the positivity criterion.

**Theorem 1.18 (endpoint_mem_Icc).**

$$endpoint \in \operatorname{Set.Icc}\left(0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint_mem_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharp endpoint lies in the permitted retention interval.

**Theorem 1.19 (compatible_of_parent).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \forall J \in \left(\operatorname{Fin}\left(4\right) \to Bool\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{IsPOVM}\left(J\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in Bool,\; E\left(i, b\right) = \sum_{(e: \operatorname{Fin}\left(4\right) \to Bool), e\left(i\right) = b} J\left(e\right)\right) \Rightarrow \operatorname{Compatible4}\left(E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.compatible_of_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A POVM with these marginal sums establishes compatibility.

**Theorem 1.20 (all_povms_compatible).**

$$\forall E \in \operatorname{Fin}\left(4\right) \to \left(Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{IsPOVM}\left(E\left(i\right)\right)\right) \Rightarrow \operatorname{Compatible4}\left(\operatorname{noisy}\left(endpoint, E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FourQubitParentConstruction.all_povms_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A compact convex sign decomposition follows from the four-vector inequality and the projection theorem. Antipodal effects give a joint parent for unbiased measurements. Each biased effect is obtained by a stochastic channel from a unit-vector effect and the two deterministic effects; applying these channels to the parent preserves every marginal.

Application correspondence: a total sign selection on the full self-adjoint qubit carrier. Here E is selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ), u is the identity, the cone is the usual positive-semidefinite cone, the norm is the matrix operator norm, and a ∘ b = (ab + ba)/2. The original inputs are all of E. The matrices X₁, X₂, X₃ are respectively [[0,1],[1,0]], [[0,−i],[i,0]], [[1,0],[0,−1]]. They are the existing pauliMatrix X, Y, Z; scalarB supplies αu + x·σ. The theorem hermitian_decomposition gives α = Re(trace a)/2 and x = bloch(a)/2 for every original a. Uniqueness is exactly BiasedTrineJointMeasurabilityThreshold.scalarB_injective. The existing scalarB_hermitian and scalarB_posSemidef_iff identify the carrier and its full cone: αu + x·σ is positive precisely when ‖x‖ ≤ α. This correspondence includes every scalar and every degenerate Bloch vector; it is not a restriction to pure states or normalized matrices.

For a = αu + x·σ and b = γu + y·σ, put K(a,b) = (ab − ba)/(2i) = (x × y)·σ and L(a,b) = α² + γ² − ‖x‖² − ‖y‖². Let ε(a,b) be +1 when L(a,b) ≤ 0, including the equality boundary, and −1 otherwise. The one total response is Dₛ(a,b) = ε(a,b)K(a,b). Equivalently, K(a,b) is imaginaryPart(ab), while a ∘ b is realPart(ab), so realPart_add_I_smul_imaginaryPart identifies ab = a ∘ b + iK(a,b). The scalarB entries reduce this equality to the usual Pauli multiplication; Xⱼ² = u, X₁X₂ = iX₃ and cyclic permutations, with reversed products negated. The construction adds no continuity, additivity, homogeneity or complex-input extension of Dₛ.

The sign rule preserves exchange and separate negation because L(b,a) = L(a,b), L(−a,b) = L(a,b) = L(a,−b); K changes sign in each of these operations. Thus Dₛ(b,a) = −Dₛ(a,b), Dₛ(−a,b) = −Dₛ(a,b) and Dₛ(a,−b) = −Dₛ(a,b). For every real angle θ, mix the ordered input-label pair itself: aθ = cos(θ)a − sin(θ)b and bθ = sin(θ)a + cos(θ)b. Both the scalar pair (α,γ) and each pair of spatial coordinates undergo the same rotation. The identity cos²(θ) + sin²(θ) = 1 gives L(aθ,bθ) = L(a,b), and bilinearity and alternation of the commutator give K(aθ,bθ) = K(a,b). Hence Dₛ(aθ,bθ) = Dₛ(a,b). This is SO(2) rotation of the two ordered labels, not merely rotation of spatial axes.

All zero rows have their original real quantifiers. For all μ and b, Dₛ(μu,b) = 0. For all s,t,r,q and a, Dₛ(su + ra, tu + qa) = 0, since the vector parts rx and qx are parallel. For all λ and a, Dₛ(a,λa²) = 0: the vector part of a² is 2αx. Equivalently these are commuting pairs, so imaginaryPart of their product vanishes before the sign is selected. Zero, repeated, proportional and scalar inputs are all included, without a nonzero or invertibility premise.

The readings range over every positive real-linear functional β : E → ℝ, with positivity meaning β(h) ≥ 0 for every positive-semidefinite h. There is no normalization premise on β(u). The vector readings βᵥ(h) = Re(v*hv) are positive for every complex vector v; Matrix.PosSemidef.of_dotProduct_mulVec_nonneg and IsHermitian.im_star_dotProduct_mulVec_self show that all positive real readings detect exactly the given cone, and applying the cone test to h and −h shows that these readings separate the full carrier. Define its complex-linear extension on the entire ambient matrix algebra by β̃(T) = β(realPart T) + iβ(imaginaryPart T). The pinned realPart_smul and imaginaryPart_smul identities supply complex linearity, and selfAdjoint.realPart_coe and selfAdjoint.imaginaryPart_coe supply agreement on every original h, not only on effects. If T is positive, its imaginary part is zero and its real part is T, so β̃ is positive. The same extension construction is an existing closed result, ProbabilisticTheory.complexExtension, in leanprover-community/physlib at revision 4e2182f2b6f0a54207a2fa62002c264217f875d6; that repository is not an admitted dependency here. EffectProbabilityExtension.effect_linear_extension alone supplies agreement on effects and must not be silently substituted for the full-carrier agreement just described.

For any finite original self-adjoint list Aⱼ, set Mⱼₖ = β̃(AⱼAₖ). This is exactly Matrix.gram ℂ (fun j => β̃.toPreGNS Aⱼ), because Aⱼ* = Aⱼ and PositiveLinearMap.preGNS_inner_def identifies each entry. Matrix.posSemidef_gram supplies positivity for every mass, including β = 0. Its transpose is positive by Matrix.PosSemidef.transpose; Hermitian symmetry identifies that transpose with entrywise complex conjugation. For the list (μu,a,b), every unit-row commutator and every diagonal commutator vanishes. Its response table Gⱼₖ = β(Aⱼ ∘ Aₖ) − iβ(Dₛ(Aⱼ,Aₖ)) is M when ε(a,b) = −1, and Mᵀ when ε(a,b) = +1. The reversed entry uses the same sign because L is exchange invariant. Thus the whole table, for all real μ and all original a,b, is positive semidefinite. Repetitions, zero labels, permutations and principal sublists are covered by Matrix.PosSemidef.submatrix; the argument does not select independent labels or normalize a reading.

Taking the a,b principal subtable gives all-mass P2. Its determinant is β(a²)β(b²) − β(a ∘ b)² − β(Dₛ(a,b))², so determinant nonnegativity is the exact bound |β(Dₛ(a,b))|² ≤ β(a²)β(b²) − β(a ∘ b)². When m = β(u) = 0, the order-unit bounds −‖h‖u ≤ h ≤ ‖h‖u give |β(h)| ≤ ‖h‖m = 0 for every original h, so the entire table is zero. Every positive mass, including subnormalized and unequal masses assigned to different readings, remains in the same argument. No identification of all positive mathematical functionals with actual preparations is used.

Actual unit translation fails. The exact coordinates give L(X₁,X₂) = −2, K(X₁,X₂) = X₃ and Dₛ(X₁,X₂) = X₃, whereas L(2u + X₁,X₂) = 2, K(2u + X₁,X₂) = X₃ and Dₛ(2u + X₁,X₂) = −X₃. Both are calls to the same total map on original matrices. The unit row being zero therefore does not force cross-axis translation invariance.

Actual vector-action fibers also fail. Use the standard identity representation of the full matrix algebra on ℂ², with its usual Hermitian inner product, ξ = (1,0)ᵀ and βξ(h) = ξ* h ξ. This representation acts by Matrix.toLinAlgEquiv′; it is irreducible since arbitrary matrices send any nonzero vector onto all of ℂ². The vector has norm one and βξ is a positive real-linear reading of mass one. PureStateHandshake.rankOneDensity ξ is its normalized positive rank-one density; pure_state_handshake supplies its idempotency and the exact identity βξ(h) = Re(trace(h rankOneDensity ξ)). Put p₋ = (u − X₃)/2, A = u + X₁, A′ = A + 2p₋ = 2u + X₁ − X₃, and B = B′ = X₂. The actual equalities are 2p₋ξ = 0, Aξ = A′ξ = (1,1)ᵀ, and Bξ = B′ξ = (0,i)ᵀ. Yet L(A,B) = −1 and K(A,B) = X₃, while L(A′,B′) = 1 and K(A′,B′) = X₁ + X₃. Consequently βξ(Dₛ(A,B)) = 1 and βξ(Dₛ(A′,B′)) = −1. Equality of input vector actions, rather than merely equality of expectations, is the fiber being tested.

The full original PB fails at the original triple (a,b,c) = (X₁,2u + X₂,0). Write v = Dₛ(a,b) − a ∘ c and w = a ∘ b + Dₛ(a,c), exactly as in the original nested calls. The inner values are Dₛ(a,b) = −X₃ and Dₛ(a,c) = 0, hence v = −X₃ and w = 2X₁. Thus r₊ = b + v = 2u + X₂ − X₃, s₊ = c + w = 2X₁, r₋ = b − v = 2u + X₂ + X₃, and s₋ = c − w = −2X₁. Both outer pairs have L = −2. Their actual outputs are Dₛ(r₊,s₊) = −2X₃ − 2X₂ and Dₛ(r₋,s₋) = 2X₃ − 2X₂. Their difference is −4X₃, whereas the PB finite-difference right-hand side −2b ∘ v − 2c ∘ w is 4X₃.

The original square-reading PB gives the same explicit failure without replacing its nested calls by a new condition. Here r±² = 6u + 4X₂ ∓ 4X₃ and s±² = 4u. Therefore r₊² + s₊² + 2Dₛ(r₊,s₊) = 10u − 8X₃ and r₋² + s₋² + 2Dₛ(r₋,s₋) = 10u + 8X₃. The same βξ reads these two original square expressions as 2 and 18, respectively. This response is consequently excluded by full PB; it supplies a separation of the stated weaker conditions and does not supply a countermodel to P2 together with full PB.

The four-label diagnostic uses the existing zero-direction mechanism, supplied generically by Matrix.PosSemidef.dotProduct_mulVec_zero_iff. For a single response D with P2, antisymmetry and full zero unit rows, let G be the actual table on (u,a,a + λu,b), h = D(a + λu,b) − D(a,b), η = β(h), q = β(b²), and z₀ = (−λ,−1,1,0)ᵀ. The original real relation −λu − a + (a + λu) = 0, Jordan bilinearity and the zero rows give z₀*Gz₀ = 0 and z₀*Ge₄ = −iη. Expanding this very table gives (z₀ − it e₄)*G(z₀ − it e₄) = t²q − 2tη for every real t. If q = 0, P2 on both original pairs forces η = 0. If η ≠ 0 then q > 0, and t = η/q gives −η²/q < 0. Nonnegativity of all these specified tilts therefore forces η = 0; separating positive readings would then force h = 0. No common-table positivity or PB-to-tilt implication is supplied by this application, and no additional generic zero-direction theorem is needed.

For the same Dₛ, take the four original labels (u,X₁,2u + X₁,X₂), λ = 2 and the same βξ. Then η = −2 and q = 1. The coefficient vector z₀ − it e₄ at t = −2 is exactly (−2,−1,1,2i)ᵀ, and its quadratic reading is exactly −4. Thus this actual four-label table is not positive, although every real-unit-anchored three-label table is positive. The complex numbers here are table coefficients only: every input to Dₛ remains an original self-adjoint matrix.

The real geometry of this translation diagnostic is spanℝ{u,a,b}. Under the stated affine zero rows, dependence of u and a makes both translated first inputs scalar and gives zero defect; if u,a are independent and the span has dimension at most two then b = su + ra and the same affine zero rows again give zero defect. Three independent real directions are therefore required for this particular nonzero translation defect. The four labels encode a redundant real relation within their at most three-dimensional span. This does not classify the minimum number of labels for arbitrary test classes. Such a span need not be closed under Jordan multiplication or D, need not have finite spectral or corner structure, and is not physical three-space. In the example X₃ lies outside spanℝ{u,X₁,X₂}.

The application reuses Pauli algebra, self-adjoint decomposition, positive-functional Gram positivity and the zero-direction mechanism. It adds no independent axiom and asserts no literature priority. Raw/PB-dependent UnitBridgeRawGeometry conclusions cannot supply a law for this response, and PauliFixedProductFamily has a different carrier. The weighted conclusions using full PB retain their own assumptions and do not apply merely because this example has the weaker symmetries and unit triples. The general JB and possibly incomplete original-domain translation and additivity bridges, the full-C* action-fiber and bilinearity equivalence and the conditional finite-table and associative-product consumers keep their original premises. There is no general JB-to-C* completion, physical realization, reduction of independent axioms, or completion of the quantum-origin objective here.

All original source obligations remain: Ω/native and full K/J/q words; parent positions and ready types; the original center and unequal-dimensional blocks; all zero, unequal and subnormalized masses; actual preparation and complete effect menus; common records and genuine grouping and forgetting; full instruments, environments and every output; actual correlated joints and recursively common-source references; every legal sequential, adaptive and parallel history with every still legal future; stopping, refusal and destruction; equal-number sides and genuine inverse returns. A mathematical matrix, positive reading or vector action supplies none of those physical sources. Born ratios require the original actual complete menu and strictly positive mass; zero mass is not normalized. Infinite CountRead, nondiscrete records, countable additivity, normality and preduals, physical clocks, energy and a common action scale ℏ each retain their source conditions.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_formula`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_neg`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_real_smul`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.B_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.Compatible4`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.all_povms_compatible`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.compatible_of_parent`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.endpoint_mem_Icc`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_complement`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_double`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.half_scalarB_posSemidef_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.hermitian_decomposition`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.noisy`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.norm_sq_coords`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_hermitian`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_posSemidef_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.scalarB_sum`
- Truth anchor: `D5/S3/Quantum/Measurement/FourQubitParentConstruction.trace_B_mul`
- Dependency: [D5/S3/Geometry/FourVectorSignSumBound](../../Geometry/FourVectorSignSumBound.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Measurement/Bloch/QubitBloch](Bloch/QubitBloch.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
