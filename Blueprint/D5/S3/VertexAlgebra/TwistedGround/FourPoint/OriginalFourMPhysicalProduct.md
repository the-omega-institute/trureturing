# Period and charge-sector normalization

## Abstract

Rank-24 transformations of the physical Gaussian product

**Definition 1.1 (Period-normalized product in each physical chart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physicalProduct`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physicalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take lattice data D with unit Gram determinant, a finite type X with maps p : X → Puncture and k : X → Fin(D.rank), and complex coordinate and weight vectors u and w on X. For either upperA, real x and chart c, use the sign ρ_c given by 1 in A, relativeB in B and relativeD in D. Set S_j = ρ_c(p_j) physicalSource(c,x,p_j,u_j) and K_ij = ρ_c(p_i)ρ_c(p_j) physicalCovariance(upperA,c,x,p_i,p_j,u_i,u_j). Write M_k for the sum of w_j S_j over marks of colour k and E = ½ ∑_{i,j∈X} w_i w_j G_{k_i,k_j} K_ij, where G is the complex cast of the original Gram matrix.

Write P_A = slitPeriod(1 − 1/x), P_B = slitPeriod(x), P_f = slitPeriod(1 − x) and P_D = dPeriod(upperA,1/x). The D period uses the lower lip for upperA = true and the upper lip for false. The spatial source uses the chosen lower D branch for either period. The theta parameters are τ_A = i P_D/P_A, τ_B = −1/(i P_B/P_f) and τ_D = −1/τ_A. In a mod-two charge sector a, the product is (P_c¹²)⁻¹ exp(E) · chargeTheta(D,hu,a,τ_c,Z), where Z = (i/(2π P_c)) M.

Here chargeTheta is the shifted theta of the doubled Gram lattice in the discriminant class corresponding to a. Its lattice sum (tsum) runs over integral charges q with reduceCharge(D,q) = a, with summand exp(π i τ_c ⟨q,q⟩_G/2 + 2π i (Gq)·Z). The Gram contraction is bilinear.

**Theorem 1.2 (Finite charge transforms of the physical products).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physical_chart_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physical_chart_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Require a unit Gram determinant, positive definiteness of the real Gram matrix, rank 24, real 0 < x < 1, and a complex radial w₀ with w₀² = 1 − 1/x and ‖w₀‖ < 1. Take either upperA and any finite mark type X with puncture and colour maps. On a neighborhood of the zero coordinate vector, the two identities hold together for every complex weight vector and every output sector a. The puncture and colour maps can repeat and coordinates can coincide.

With the coordinates and weights held fixed across charts, write F_c(a) for physicalProduct. Then F_D(a) = 2⁻¹² ∑_b fourierSign(D,a,b) F_A(b), and F_B(a) = (periodRoot(A,x)¹²)⁻¹ · 2⁻¹² ∑_b fourierSign(D,a,b) quadraticSign(D,b) F_A(b). Each sum runs over all 2²⁴ mod-two charge sectors b. The A period root is (√x)⁻¹ with the positive real square root.

In the native A disk, square the marked half-coordinates to recover the inverse lowering coordinates and divide each weight by the A half-Jacobian. The signed source and regular covariance transports identify the finite product with the native chart product times exp(−E_R). Here E_R is the Gram-weighted quadratic sum of the A same-puncture lowering correction in the rescaled weights. This factor is common to every chart and charge sector.

For the B transform, the period before inversion is t_B = i P_B/P_f. The A period ratio is τ_A = t_B + 1 on the lower D lip and t_B − 1 on the upper D lip. The translation contributes quadraticSign(D,b). The B inversion gives the negative of the B theta source, which has the same theta value because charge negation preserves each mod-two sector. The Pfaff period relation P_f = periodRoot(A,x) P_A gives the additional factor in F_B.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physicalProduct`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physical_chart_product`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance](OriginalFourMPhysicalCovariance.md)
