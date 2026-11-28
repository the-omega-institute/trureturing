# Equilateral spherical angle variation

## Abstract

An explicit family of equilateral unit-sphere triangles has all tangent-projection angle derivatives equal to one and spherical excess derivative equal to three.

**Definition 1.1 (Equilateral vertices).**

Lean statement: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalVertices`

*Formalization.* `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real parameter t, put r = cos(t)/(1 − cos(t)), a = √(1 − r), and b = (√(1 + 2r) − a)/3. The three vectors p_i in Euclidean three-space have coordinates (p_i)_k = a δ_ik + b for i,k ∈ {0,1,2}.

**Definition 1.2 (Tangent-projection angle).**

Lean statement: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalAngle`

*Formalization.* `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalAngle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At vertex i, set x = p_j − ⟨p_i,p_j⟩p_i and y = p_k − ⟨p_i,p_k⟩p_i. The angle A_ijk(t) is arccos(⟨x,y⟩/(‖x‖‖y‖)).

**Definition 1.3 (Spherical excess).**

Lean statement: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalExcess`

*Formalization.* `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equal-angle spherical excess E(t) is defined by 3t − π.

**Theorem 1.4 (Unit vertices and angle and excess derivatives).**

Lean statement: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.equilateral_spherical_angle_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.equilateral_spherical_angle_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t with π/3 < t < π, each of the three vertices has norm one. For every pairwise distinct triple i,j,k ∈ {0,1,2}, the function s ↦ A_ijk(s) has derivative 1 at t. The function E has derivative 3 at t, the sum of the three derivatives of A_i,i+1,i+2 at t equals E′(t), where indices are taken modulo three, and E′(t) is nonzero.

Strict monotonicity of cosine on [0,π] gives −1/2 < r < 1. The square-root identities yield a² = 1 − r and 2ab + 3b² = r. Consequently the Gram matrix has diagonal entries one and all off-diagonal entries r. For distinct i,j,k, the two tangent projections have squared norms 1 − r² > 0 and inner product r − r². Their normalized inner product is (r − r²)/(1 − r²) = cos(t). Taking arccos on this interval gives A_ijk(t) = t. The interval is open, so the equality holds on a neighborhood of each t and gives derivative one there. Differentiating the affine excess and summing three cyclic derivatives gives the result.

The strict interval bounds ensure the Gram eigenvalues 1 − r and 1 + 2r are positive and the tangent projections are nonzero. At π/3 the Gram matrix degenerates to r = 1, and at π the value r = −1/2 gives a degenerate Gram matrix. The classical Girard theorem identifies spherical excess with intrinsic area for a nondegenerate geodesic triangle on the unit sphere. That geometric area identification is external to the formal result, which concerns the explicit tangent angles and the defined scalar excess.

## References

- Truth anchor: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.equilateral_spherical_angle_variation`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalAngle`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalExcess`
- Truth anchor: `D5/S3/Geometry/DiscreteGravity/EquilateralSphericalAngleVariation.sphericalVertices`
