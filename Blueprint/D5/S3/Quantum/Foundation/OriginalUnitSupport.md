# Original unit and common matrix support

## Abstract

An arbitrary strictly positive original unit admits a state carrying the entire native PSD support.

Let F be a real or complex scalar field, represented by RCLike, and let iota be any finite decidable matrix index type. V is a nonzero finite dimensional real vector space. C is a pointed cone whose real linear span is V. The real linear map rho is injective and sends every member of C to a positive semidefinite native F-matrix. The original real linear unit u is strictly positive on every nonzero member of C. No trace normalization, positive definite ambient representative, rank-one generation, closedness, or compactness is needed for this support result.

**Definition 1.1 (Native common support).**

$$\forall F \in Type,\; \forall iota \in Type,\; \forall V \in Type,\; [\operatorname{RCLike}\left(F\right)] [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, V, \operatorname{Matrix}\left(iota, iota, F\right)\right),\; \operatorname{commonSupport}\left(C, rho\right) = \operatorname{iSup}\left(x\in C\mapsto \operatorname{range}\left(\operatorname{toEuclideanLin}\left(rho(x)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/OriginalUnitSupport.commonSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum is in the lattice of F-linear subspaces of EuclideanSpace F iota and ranges over every original cone element. Thus a complex support has its complex dimension; it is not a realification. toEuclideanLin is the matrix action in the usual orthonormal coordinates.

**Theorem 1.2 (An original state with the entire common support).**

$$\forall F \in Type,\; \forall iota \in Type,\; \forall V \in Type,\; [\operatorname{RCLike}\left(F\right)] [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{R}, V\right)\right) \Rightarrow \left(\forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0 < u(x)\right)\right) \Rightarrow \left(\forall rho \in \operatorname{LinearMap}\left(\mathbb{R}, V, \operatorname{Matrix}\left(iota, iota, F\right)\right),\; \operatorname{Injective}\left(rho\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \operatorname{PosSemidef}\left(rho(x)\right)\right) \Rightarrow \left(\exists y \in V,\; y\in C \land \left(u(y) = 1 \land \left(\left(\forall z \in iota\to F,\; \operatorname{mulVec}\left(rho(y), z\right) = 0 \Leftrightarrow \left(\forall x \in V,\; \operatorname{mulVec}\left(rho(x), z\right) = 0\right)\right) \land \left(\operatorname{range}\left(\operatorname{toEuclideanLin}\left(rho(y)\right)\right) = \operatorname{commonSupport}\left(C, rho\right) \land \left(\forall z \in \operatorname{EuclideanSpace}\left(F, iota\right),\; z\in \operatorname{commonSupport}\left(C, rho\right) \Rightarrow \left(z\neq 0 \Rightarrow 0 < \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{ofLp}\left(z\right)\right), \operatorname{mulVec}\left(rho(y), \operatorname{ofLp}\left(z\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalUnitSupport.exists_original_unit_full_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite dimensionality selects a finite spanning subset of the original cone. For its sum a, positive semidefiniteness makes a zero quadratic value force each summand to annihilate the same vector. Real spanning then propagates this annihilation to every represented original vector. Injectivity and nontriviality ensure a is nonzero. Hence u(a) is strictly positive and y = a / u(a) is an actual original state with exactly the same kernel. Hermitian orthogonal range-kernel duality identifies its range with the entire common support. A nonzero vector in that support has strictly positive quadratic value: otherwise it belongs to both the range and its orthogonal complement. This allows support-deficient ambient representations and includes support dimension one. ofLp denotes the ordinary coordinate vector of a Euclidean vector; re is the real part.

The result supplies the original-unit positive-on-support candidate needed before determinant normalization. It does not construct support coordinates, the determinant maximizer, its uniqueness or stationarity, inverse-square-root congruence, a trace-preserving cone equivalence, or the returned order unit. Whole-base, pure-point, dual-effect, confirmation, exclusion, face and rank transport, together with fixed-complement and frame conclusions, require those further constructions. No classification or physical realization is inferred. The finite spanning, PSD quadratic-form and orthogonal-complement tools are standard; no literature priority is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalUnitSupport.commonSupport`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalUnitSupport.exists_original_unit_full_support`
