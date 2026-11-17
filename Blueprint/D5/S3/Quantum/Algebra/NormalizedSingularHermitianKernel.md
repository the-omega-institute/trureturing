# Normalized singular Hermitian kernel geometry

## Abstract

Normalized singular Hermitian kernels reduce to a common vector, a neutral plane, or an i-skew primitive form.

All matrices below have type M = Matrix (Fin 3) (Fin 3) ℂ. The coordinate layer keeps real diagonal entries, conjugate-symmetric off-diagonal entries, the determinant pencil, the shear and final unitary congruences, and the complete vector, neutral-plane, and primitive alternatives.

**Definition 1.1 (The three-by-three matrix type).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.M`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M is the abbreviation Matrix (Fin 3) (Fin 3) ℂ.

**Definition 1.2 (The signature matrix).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.D`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is the matrix with diagonal entries 1, -1, 0 and all off-diagonal entries zero.

**Definition 1.3 (Hermitian coordinate matrix).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a,b : ℝ and z,u,v : ℂ, hermitianMatrix a b z u v is the matrix with rows [(a,z,u), (conj z,b,v), (conj u,conj v,0)], with real numbers coerced to ℂ.

**Definition 1.4 (The shear matrix).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p : ℂ, shear p is the lower triangular matrix [[1,0,0],[0,1,0],[0,-p,1]].

**Definition 1.5 (The final unitary matrix).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

finalUnitary is the displayed 3-by-3 matrix built from Real.sqrt 2, its inverse, and Complex.I: rows [(r⁻¹,I*r⁻¹,0),(r⁻¹,-I*r⁻¹,0),(0,0,I)] with r = sqrt 2.

**Definition 1.6 (The real skew set).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.skew3`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.skew3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

skew3 is the set of matrices ∃ x y z : ℝ, A = [[0,x,y],[-x,0,z],[-y,-z,0]] after coercion to ℂ.

**Definition 1.7 (The i-skew set).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.iSkew3`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.iSkew3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

iSkew3 is the set of matrices ∃ x y z : ℝ, A = I • [[0,x,y],[-x,0,z],[-y,-z,0]] after coercion to ℂ.

**Definition 1.8 (The third coordinate vector).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.e3`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.e3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

e3 : Fin 3 → ℂ is ![0,0,1].

**Definition 1.9 (A neutral graph generator).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.neutralGenerator`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.neutralGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

neutralGenerator c : Fin 3 → ℂ is ![1,-c,0] for c : ℂ.

**Theorem 1.10 (Coordinates of every Hermitian matrix).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitian_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitian_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H : M with H.IsHermitian, there exist a,b,c : ℝ and z,u,v : ℂ such that H = [[a,z,u],[conj z,b,v],[conj u,conj v,c]] with real entries coerced to ℂ.

**Theorem 1.11 (The general determinant pencil).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.determinant_pencil_general`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.determinant_pencil_general` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all a,b,c,t : ℝ and z,u,v : ℂ, det(D + (t : ℂ) • [[a,z,u],[conj z,b,v],[conj u,conj v,c]]) equals -(t:ℂ)*(c:ℂ) + (t:ℂ)^2*((b:ℂ)*(c:ℂ)-(a:ℂ)*(c:ℂ)+conj u*u-conj v*v) + (t:ℂ)^3*((a:ℂ)*(b:ℂ)*(c:ℂ)-(a:ℂ)*(conj v*v)-(b:ℂ)*(conj u*u)+z*v*conj u+conj z*conj v*u-(c:ℂ)*(z*conj z)).

**Theorem 1.12 (The coordinate determinant).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix_det`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all a,b : ℝ and z,u,v : ℂ, det(hermitianMatrix a b z u v) = -(a:ℂ)*(conj v*v) - (b:ℂ)*(conj u*u) + z*v*conj u + conj z*conj v*u.

**Theorem 1.13 (The shear congruence identity).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b : ℝ and p,u : ℂ satisfying (a+b : ℂ) = conj p*u + p*conj u, shear pᴴ * hermitianMatrix a b (p*u) u (conj u) * shear p = [[a,0,u],[0,-a,conj u],[conj u,u,0]].

**Theorem 1.14 (The final unitary identity).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.final_unitary_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.final_unitary_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,x,y : ℝ, finalUnitaryᴴ * [[a,0,x+I*y],[0,-a,x-I*y],[x-I*y,x+I*y,0]] * finalUnitary = I • [[0,a,sqrt 2*x],[-a,0,sqrt 2*y],[-sqrt 2*x,-sqrt 2*y,0]], with real entries coerced to ℂ.

**Theorem 1.15 (The final unitary is invertible).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary_isUnit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsUnit (finalUnitary : M).

**Theorem 1.16 (The zero graph gives a common kernel).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.zero_graph_common_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.zero_graph_common_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K : Submodule ℝ M, if ∀ H ∈ K, H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0, then ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0.

**Theorem 1.17 (Universal coefficient constraints).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_coefficient_constraints`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_coefficient_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K : Submodule ℝ M with D ∈ K, every H ∈ K Hermitian, and det H = 0 for every H ∈ K, one has ∀ H ∈ K, H 2 2 = 0 ∧ conj(H 0 2)*H 0 2 = conj(H 1 2)*H 1 2.

**Theorem 1.18 (Faithful singular coordinates).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_faithful_coordinate_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_faithful_coordinate_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same K, D, Hermitian, and singular hypotheses, every H ∈ K has ∃ a b : ℝ, ∃ z u v : ℂ, H = hermitianMatrix a b z u v ∧ conj u*u = conj v*v ∧ ((a+b : ℝ) : ℂ)*(conj u*u) = z*v*conj u + conj z*conj v*u.

**Theorem 1.19 (A common graph orientation).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_common_graph_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_common_graph_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same K, D, Hermitian, and singular hypotheses, ∃ c : ℂ, ‖c‖ = 1 ∧ ((∀ H ∈ K, H 1 2 = c * H 0 2) ∨ (∀ H ∈ K, H 1 2 = c * conj(H 0 2))).

**Theorem 1.20 (The linear graph alternative).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.linear_graph_common_kernel_or_neutral_plane`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.linear_graph_common_kernel_or_neutral_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, and hgraph : ∀ H ∈ K, H 1 2 = c*H 0 2, either ∃ v ≠ 0 with ∀ H ∈ K, H*ᵥv=0, or ∃ W : Submodule ℂ (Fin 3 → ℂ), finrank ℂ W = 2 and ∀ H ∈ K, ∀ w,w' ∈ W, star w ⬝ᵥ (H*ᵥw')=0.

**Theorem 1.21 (The proper conjugate graph alternative).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.conjugate_graph_proper_image_common_kernel_or_neutral_plane`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.conjugate_graph_proper_image_common_kernel_or_neutral_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, hgraph : ∀ H ∈ K, H 1 2 = c*conj(H 0 2), and hnotonto : ¬∀ u : ℂ, ∃ H ∈ K, H 0 2 = u, the same common-vector or finrank-two neutral-plane disjunction holds.

**Definition 1.22 (The normalized graph trichotomy).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.normalizedGraphTrichotomy`

*Formalization.* `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.normalizedGraphTrichotomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedGraphTrichotomy is the proved proposition ∀ K : Submodule ℝ M, D ∈ K → (∀ H ∈ K, H.IsHermitian) → (∀ H ∈ K, H.det = 0) → (∃ v ≠ 0, ∀ H ∈ K, H*ᵥv=0) ∨ (∃ W, finrank ℂ W=2 ∧ ∀ H ∈ K, ∀ w,w'∈W, star w ⬝ᵥ(H*ᵥw')=0) ∨ (∃ C : M, IsUnit C ∧ ∀ H, H ∈ K ↔ Cᴴ*H*C ∈ iSkew3). Its proposition follows by combining the common graph orientation with the linear, proper conjugate, and surjective conjugate alternatives; NativeThreeKernelGeometry establishes this trichotomy and then excludes the primitive alternative for native compressions.

**Theorem 1.23 (The surjective conjugate primitive).**

Lean statement: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.surjective_conjugate_graph_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.surjective_conjugate_graph_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K,D,hHerm,hSing, c : ℂ with ‖c‖ = 1, hgraph : ∀ H ∈ K, H 1 2 = c*conj(H 0 2), and honto : ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u, there exists C : M with IsUnit C and ∀ H : M, H ∈ K ↔ Cᴴ * H * C ∈ (iSkew3 : Set M).

## References

- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.D`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.M`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.conjugate_graph_proper_image_common_kernel_or_neutral_plane`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.determinant_pencil_general`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.e3`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.finalUnitary_isUnit`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.final_unitary_identity`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitianMatrix_det`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.hermitian_coordinates`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.iSkew3`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.linear_graph_common_kernel_or_neutral_plane`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.neutralGenerator`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.normalizedGraphTrichotomy`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.shear_identity`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.skew3`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.surjective_conjugate_graph_primitive`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_coefficient_constraints`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_common_graph_orientation`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.universal_faithful_coordinate_representation`
- Truth anchor: `D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel.zero_graph_common_kernel`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](CommonCoefficientPlane.md)
