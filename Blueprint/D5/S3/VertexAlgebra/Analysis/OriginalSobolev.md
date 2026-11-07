# Original Hermitian Sobolev spaces

## Abstract

Hilbert and Sobolev completions of the original positive-lattice Hermitian form.

**Theorem 1.1 (embed norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, every natural k and finite original v, the norm of embed k v equals normD of (1+L0)^k v. The completion embedding is an isometry for the actual pulled-back Hermitian form.

**Theorem 1.2 (embed inner).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_inner`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model and finite original v,w, the order-zero embedded inner product equals the full original Hm(v,w).

**Theorem 1.3 (embed injective).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model and natural k, embed k is injective, by the original completion embedding of the definite pulled-back norm.

**Theorem 1.4 (embed dense).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_dense`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model and natural k, embed k has dense range in the actual Sobolev k completion.

**Theorem 1.5 (projection grade).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.projection_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.projection_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original k and integer grades E,n, an original v of grade E projects at n to embed k v when E=n, and to zero otherwise. Both inverse-Gram equations and original Hm orthogonality are retained.

**Theorem 1.6 (sobolev grade norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.sobolev_grade_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.sobolev_grade_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, natural k,E and original v of grade E, normD((1+L0)^k v)=(E+1)^k normD(v). No nonzero-vector or positive-rank hypothesis is required.

**Theorem 1.7 (inclusion embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.inclusion_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.inclusion_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, natural j<=k and finite original v, inclusion j k sends embed k v to embed j v.

**Theorem 1.8 (truncation grade).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, natural k, finite set F of integer grades and original v of grade E, truncation k F fixes embed k v when E is in F and is zero otherwise.

**Theorem 1.9 (truncation norm).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, natural k, finite set F of integer grades and arbitrary completed x in Sobolev k, the truncation norm is at most the norm of x. Orthogonality gives the Pythagorean comparison in the actual completed metric.

**Theorem 1.10 (truncation embed of subset).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_embed_of_subset`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_embed_of_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, natural k, original finite v and finite integer set F containing stateEnergies D v, truncation k F fixes embed k v.

Model retains LatticeData D, positive definiteness of gramReal(D), and a complex matrix H with both H*gramComplex(D)=1 and gramComplex(D)*H=1. The finite carrier is the original finite charge sum of oscillator polynomials, with its original mixed-colour Hermitian form Hm and normD=sqrt(Re Hm(v,v)). Positivity is reused from OriginalCurrentEnergy through the invertible real full frame and FactorialFockMetric; original monomials are not assumed orthogonal.

Set T=1+sugawaraMode(D,H,0). Finite(k) has literally Carrier(D) as its elements and the pulled-back inner product Hm(T^k u,T^k v). The coefficient formula for T^k multiplies a label of energy E by (E+1)^k. Nonnegativity of the original energies makes every such multiplier nonzero, proving injectivity and hence definiteness of the pulled-back form. Sobolev(k)=H_k is its Mathlib UniformSpace.Completion; Hilbert=H_0. The linear embedding of finite states is injective and dense, has norm normD(T^k v), and at order zero preserves exactly Hm.

completedGrade(k,n) is the range of the embedded original algebraic grade, without taking an additional closure. Its finite dimensionality proves that this range is already closed and complete. The orthogonal projection onto it agrees with the original gradeProjection on finite states. A finite sum of these projections is a genuine algebraic truncation even on a completed vector. Orthogonality makes truncations contractions, and density of finite states proves that the net over finite subsets of integer grades converges to each vector in every H_k.

For j<=k the original identity extends to inclusion(j,k):H_k->H_j by the monotone energy norms. These maps agree with finite embeddings, compose coherently, and commute with grade projections. Totality of the projections and their algebraic ranges prove that every inclusion is injective. OriginalModeExtension uses the norms, dense embeddings and inclusions; OriginalSmoothDomain uses their injectivity and compatibility; OriginalSmearingCore uses the algebraic convergent truncations for graph approximation and sector identification.

The module supplies the actual completions, consumed analytic interfaces and proof components for original smooth fields and heat. Completion, bounded extension, projection and finite-dimensional closedness use Mathlib under its existing Apache 2.0 attribution. The original lattice and Hermitian-form suppliers retain their source attributions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_dense`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_injective`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_inner`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.embed_norm`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.inclusion_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.projection_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.sobolev_grade_norm`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_embed_of_subset`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalSobolev.truncation_norm`
- Dependency: [D5/S3/VertexAlgebra/Lattice/OriginalChargedEnergy](../Lattice/OriginalChargedEnergy.md)
