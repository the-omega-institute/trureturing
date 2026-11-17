# The original continuous spin carrier

## Abstract

Coordinate recovery and output normality for a total skew relation on the original continuous spin sections.

A section is represented by its four continuous real coordinate functions, with coordinate zero along the unit and coordinates one through three along the fixed orthonormal axes. This is the coordinate presentation of C(T, R u plus R^3). The source norm is the supremum of abs(alpha) plus sqrt(x1^2+x2^2+x3^2), and the positive cone is alpha >= sqrt(x1^2+x2^2+x3^2) pointwise. The auxiliary energy alpha^2+x1^2+x2^2+x3^2 used below is a different quadratic expression, not a replacement norm.

Original(T) consists of a real linear subspace E closed under the specified spin Jordan product and containing every constant four-coordinate section. The coefficient algebra A is exactly the continuous functions f whose central section (f,0,0,0) belongs to E. No density, completeness, inverse closure or square-root closure is imposed. The algebraic statements hold for every topological T, hence in particular for the nonempty compact Hausdorff source domain.

**Theorem 1.1 (All four coefficients belong to the actual coefficient algebra).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall a \in \operatorname{Sections}\left(T\right),\; \operatorname{mem}\left(a, \operatorname{carrier}\left(E\right)\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{mem}\left(\operatorname{a}\left(i\right), \operatorname{scalarAlgebra}\left(E\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.original_four_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice multiplying by an axis gives the projection onto the unit and that axis. Half the sum of the three such projections minus the original section isolates the scalar component. Subtract it from each axis projection and multiply by that axis to recover each vector coefficient along the unit. Conversely, Jordan multiplication of each central coefficient by the corresponding constant axis reconstructs the section. Uniqueness follows from equality of the four coordinate functions.

**Theorem 1.2 (Two raw moments force pointwise normality).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall a \in \operatorname{Elem}\left(E\right),\; \forall b \in \operatorname{Elem}\left(E\right),\; \forall t \in T,\; \operatorname{scalarAt}\left(\operatorname{D}\left(R, a, b\right), t\right) = 0 \land \left(\operatorname{vectorDotAt}\left(a, \operatorname{D}\left(R, a, b\right), t\right) = 0 \land \operatorname{vectorDotAt}\left(b, \operatorname{D}\left(R, a, b\right), t\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_output_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Raw(E) supplies the same total D:E x E -> E, skewness, the full Jordan PY identity, and D(a,D(a,b))=H_a(b). It supplies no additivity, continuity, real homogeneity, point-evaluation descent, Jacobi or associator law. Write p=D(a,b), rho=x dot x and Gamma=rho(y dot y)-(x dot y)^2. PY gives energy(p)=Gamma. PY at (a,p), followed by NN and the polynomial identity energy(H_a(b))=rho Gamma, gives rho p0^2+(x dot p)^2=0. Positivity forces x dot p=0; if rho is nonzero it also forces p0=0, while rho=0 makes Gamma and every coordinate of p zero. Skewness gives orthogonality to the other input. These statements concern actual original outputs, without defining a quotient relation at a point.

**Theorem 1.3 (Constancy on an original H fibre).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall a \in \operatorname{Elem}\left(E\right),\; \forall b \in \operatorname{Elem}\left(E\right),\; \forall c \in \operatorname{Elem}\left(E\right),\; \operatorname{H}\left(E, a, b\right) = \operatorname{H}\left(E, a, c\right) \Rightarrow \operatorname{D}\left(R, a, b\right) = \operatorname{D}\left(R, a, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_h_fibre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing NN once more gives H_a(D(a,b))=D(a,H_a(b)). For equal H images, the two outputs have equal H images. Normality makes H_a act as minus rho on both outputs. Where rho is nonzero it cancels; where rho vanishes, PY makes both outputs zero.

**Theorem 1.4 (Real homogeneity in both slots).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall a \in \operatorname{Elem}\left(E\right),\; \forall b \in \operatorname{Elem}\left(E\right),\; \forall r \in Real,\; \operatorname{D}\left(R, a, \operatorname{smul}\left(r, b\right)\right) = \operatorname{smul}\left(r, \operatorname{D}\left(R, a, b\right)\right) \land \operatorname{D}\left(R, \operatorname{smul}\left(r, a\right), b\right) = \operatorname{smul}\left(r, \operatorname{D}\left(R, a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_real_homogeneity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original H-fibre constancy gives shears. Six real shears give the determinant-one diagonal action. Applying NN to the scaled first input and inverse-scaled second input gives F_a(r F_a(b))=r H_a(b). One more composition and normality cancel H_a on the two relevant outputs, proving homogeneity. The zero multiplier is treated by PY.

**Theorem 1.5 (Independence of both central parts).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall a \in \operatorname{Elem}\left(E\right),\; \forall b \in \operatorname{Elem}\left(E\right),\; \operatorname{D}\left(R, a, b\right) = \operatorname{D}\left(R, \operatorname{vectorPart}\left(E, a\right), \operatorname{vectorPart}\left(E, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_scalar_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H_a is independent of the scalar part of its argument. H-fibre constancy and skewness therefore remove the two central parts without assuming additivity of D.

**Theorem 1.6 (The nested original K identity).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall x \in \operatorname{Vectors}\left(E\right),\; \forall y \in \operatorname{Vectors}\left(E\right),\; \operatorname{K}\left(R, x, \operatorname{K}\left(R, x, y\right)\right) = \operatorname{smul}\left(\operatorname{dot}\left(x, y\right), x\right) - \operatorname{smul}\left(\operatorname{dot}\left(x, x\right), y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_nested` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is defined by restricting the same D to scalar-free original inputs and retaining its three coefficient functions in A. Scalar-zero output identifies the embedded K output with the original D output. The original NN equality then gives the displayed identity.

**Theorem 1.7 (Orthogonality and area on the actual coefficient module).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall x \in \operatorname{Vectors}\left(E\right),\; \forall y \in \operatorname{Vectors}\left(E\right),\; \operatorname{dot}\left(\operatorname{K}\left(R, x, y\right), x\right) = 0 \land \left(\operatorname{dot}\left(\operatorname{K}\left(R, x, y\right), y\right) = 0 \land \left(\operatorname{dot}\left(\operatorname{K}\left(R, x, y\right), \operatorname{K}\left(R, x, y\right)\right) = \operatorname{dot}\left(\operatorname{cross}\left(x, y\right), \operatorname{cross}\left(x, y\right)\right) \land \left(\forall r \in Real,\; \operatorname{K}\left(R, x, \operatorname{smul}\left(r, y\right)\right) = \operatorname{smul}\left(r, \operatorname{K}\left(R, x, y\right)\right) \land \operatorname{K}\left(R, \operatorname{smul}\left(r, x\right), y\right) = \operatorname{smul}\left(r, \operatorname{K}\left(R, x, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise normality gives the two dot equalities as identities in the actual scalar algebra. The scalar component of PY gives the area equality, using the cross-dot-cross identity over a commutative ring. Real homogeneity of the same original D gives both real homogeneities of K.

**Theorem 1.8 (Translation by an original H-kernel vector).**

$$\forall T \in TopologicalSpaces,\; \forall E \in \operatorname{Original}\left(T\right),\; \forall R \in \operatorname{Raw}\left(E\right),\; \forall x \in \operatorname{Vectors}\left(E\right),\; \forall y \in \operatorname{Vectors}\left(E\right),\; \forall c \in \operatorname{Vectors}\left(E\right),\; \operatorname{smul}\left(\operatorname{dot}\left(x, c\right), x\right) - \operatorname{smul}\left(\operatorname{dot}\left(x, x\right), c\right) = 0 \Rightarrow \operatorname{K}\left(R, x, y + c\right) = \operatorname{K}\left(R, x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_kernel_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is the actual polynomial H_x(c)=0 in A^3. The same original H-fibre theorem gives K(x,y+c)=K(x,y), without additivity of K.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.original_four_components`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_geometry`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_kernel_translation`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_K_nested`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_h_fibre`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_output_normal`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_real_homogeneity`
- Truth anchor: `D5/S3/Quantum/Algebra/UnitBridgeRawGeometry.raw_scalar_independent`
