# Original finite readout and real polarization

## Abstract

The original real-scalar three-path law derives a positive real bilinear polar without assuming additivity of the marker or regularity of the readout.

**Definition 1.1 (The unchanged original relation).**

$$\forall (V : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)], \forall (U : (V \to V)), \forall (q : (V \to \mathbb{R})), \operatorname{Balance}\left(U, q\right) \iff (\forall (x : V), \forall (y : V), \forall (t : \mathbb{R}), (\operatorname{q}\left(x + t \cdot y\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(x + t \cdot \operatorname{U}\left(y\right)\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(t \cdot \operatorname{U}\left(x\right) + y\right) - \operatorname{q}\left(0\right)) = 2 \cdot (\operatorname{q}\left(x\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(y\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(t \cdot x\right) - \operatorname{q}\left(0\right)) + 2 \cdot (\operatorname{q}\left(t \cdot y\right) - \operatorname{q}\left(0\right)))$$

*Formalization.* `D5/S3/QuadraticForms/RealThreePathPolar.Balance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V is an arbitrary real vector space. U is an arbitrary function, and q is finite real-valued. Q(x) abbreviates q(x)-q(0), using the same original baseline in every occurrence. In particular Q(tx) and Q(ty) remain original readouts, with no homogeneity assumption. No topology, U(0)=0, additivity, linearity, periodicity or norm is supplied.

**Theorem 1.2 (A derived positive real bilinear polar and actual radical).**

$$\forall (V : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)], \forall (U : (V \to V)), \forall (q : (V \to \mathbb{R})), ((\forall (x : V), 0 \le \operatorname{q}\left(x\right)) \land (\operatorname{Balance}\left(U, q\right))) \Rightarrow \exists (B : \operatorname{LinearMap}\left(\mathbb{R}, V, \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right)), (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) = \frac{\operatorname{q}\left(x + y\right) - \operatorname{q}\left(x - y\right)}{4}) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) = \operatorname{B}\left(y, x\right)) \land (\forall (x : V), \operatorname{q}\left(x\right) = \operatorname{q}\left(0\right) + \operatorname{B}\left(x, x\right)) \land (\forall (x : V), 0 \le \operatorname{B}\left(x, x\right)) \land (\forall (x : V), \operatorname{B}\left(\operatorname{U}\left(x\right), \operatorname{U}\left(x\right)\right) = \operatorname{B}\left(x, x\right)) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) + \operatorname{B}\left(x, \operatorname{U}\left(y\right)\right) + \operatorname{B}\left(\operatorname{U}\left(x\right), y\right) = 0) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(\operatorname{U}\left(x\right), \operatorname{U}\left(y\right)\right) = \operatorname{B}\left(x, y\right)) \land (\forall (x : V), (\operatorname{B}\left(x, x\right) = 0) \iff x \in \operatorname{ker}\left(B\right)) \land (\forall (x : V), x + \operatorname{U}\left(x\right) + \operatorname{U}\left(\operatorname{U}\left(x\right)\right) \in \operatorname{ker}\left(B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RealThreePathPolar.raw_real_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B ranges over real bilinear maps V by V to the real numbers, and ker(B) is the kernel of the real-linear map x mapped to B(x,-). All displayed properties hold for one and the same derived B. Thus its diagonal zero set is an actual real subspace, rather than an assumed quotient certificate.

Exchanging the original inputs cancels the two marker terms. The resulting scalar exchange relation separates an additive odd part A from an even part E. A finite sqrt(2) substitution gives E(2x)=4E(x); a finite translate recurrence gives the parallelogram identity. TauCeti.QuadraticMap.ofParallelogram is then applied directly, supplying the integer quadratic map and its existing bilinear polar companion.

The nonnegative original q bounds E below. Integer scaling and the Archimedean order force E to be nonnegative; on its zero set the same argument forces A to vanish. The scalar exchange relation gives b(x,ty)=b(tx,y). For each fixed x, the additive scalar function t mapped to b(tx,x) is nonnegative on nonnegative t by the square-root substitution. Monotonicity and rational sandwiches identify it with t b(x,x). Polarizing this identity proves actual real bilinearity on the original real vector space.

The original relation at x=y=0 makes U(0) invisible. It then gives Q(tU(x))=Q(tx), both even and odd invariance, and the three-direction bilinear relation. That relation forces additivity of U modulo the radical; diagonal invariance then yields full bilinear isometry. The orbit sum x+U(x)+U(U(x)) is radical. Since A vanishes there and is marker-invariant, 3A(x)=0. This proves the complete odd drift vanishes, not merely that it is additive.

The lower-bound and Archimedean scalar estimates in raw_even_data and real_polar supply the real scalar structure. This result supplies original_visible_quotient and the original real-linear Hilbert characterization. The representation describes the original readouts; physical preparations require their own realization assumptions.

### Application: all-angle two-output characterization

Let V be any real vector space, in any universe, and let A : V to the real numbers satisfy A(x) >= 0 for every x. Thus all readouts are finite. The following equivalence uses every real coefficient pair c,s with c squared plus s squared equal to one, including both signs. The existential quantifier is unique. IsPosSemidef means symmetry and a nonnegative diagonal, exactly as in LinearMap.BilinForm.IsPosSemidef.

$$
\forall (V : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)], \forall (A : (V \to \mathbb{R})), (\forall (x : V), 0 \le \operatorname{A}\left(x\right)) \Rightarrow ((\forall (x : V), \forall (y : V), \forall (c : \mathbb{R}), \forall (s : \mathbb{R}), (c \cdot c + s \cdot s = 1) \Rightarrow \operatorname{A}\left(c \cdot x + s \cdot y\right) + \operatorname{A}\left(-s \cdot x + c \cdot y\right) = \operatorname{A}\left(x\right) + \operatorname{A}\left(y\right)) \iff (\exists! (B : \operatorname{BilinForm}\left(\mathbb{R}, V\right)), (\operatorname{IsPosSemidef}\left(B\right)) \land (\forall (x : V), \operatorname{A}\left(x\right) = \operatorname{A}\left(0\right) + \operatorname{B}\left(x, x\right))))
$$

Put a0=A(0) and q(x)=A(x)-a0. Subtracting the same two baseline terms preserves the rotation-total law and gives q(0)=0. The coefficients (0,1), with second input zero, give q(-x)=q(x). Put r=1/sqrt(2). Applying the law to (z,0) at (r,r) gives 2q(rz)=q(z). Applying it to (x,y) at the same coefficients, using evenness and this scaling at x+y and x-y, gives q(x+y)+q(x-y)=2q(x)+2q(y).

Apply TauCeti.QuadraticMap.ofParallelogram with f=q, codomain the real numbers, and injectivity of multiplication by two. Its integer quadratic map E evaluates to q at every original vector. The original nonnegativity assumption gives E(x) >= -a0. Apply quadratic_nonneg with c=a0 to obtain E(x) >= 0. This step allows arbitrary nonnegative baselines; it does not assume that the centered response is positive in advance.

For any real t, take d=sqrt(1+t squared)>0 and coefficients (1/d,t/d). Rotation of the pair (dx,dy), followed by the two axis cases (dx,0) and (dy,0), gives E(x+ty)+E(tx-y)=E(x)+E(tx)+E(y)+E(ty). Here evenness replaces E(-tx+y) by E(tx-y). Subtracting the parallelogram identity E(tx+y)+E(tx-y)=2E(tx)+2E(y) gives the precise scalar-exchange premise below. No scalar homogeneity has been supplied.

$$
\forall (x : V), \forall (y : V), \forall (t : \mathbb{R}), \operatorname{E}\left(x + t \cdot y\right) - \operatorname{E}\left(t \cdot x + y\right) = \operatorname{E}\left(x\right) - \operatorname{E}\left(y\right) - \operatorname{E}\left(t \cdot x\right) + \operatorname{E}\left(t \cdot y\right)
$$

Apply real_polar to this same E, its nonnegativity, and this exchange identity. It gives one real bilinear form B with B(x,y)=(E(x+y)-E(x)-E(y))/2, B(x,y)=B(y,x), and B(x,x)=E(x). The positive_additive_scalar argument inside real_polar derives real linearity from positivity of an additive scalar function. The diagonal identity and nonnegativity give IsPosSemidef, and A(x)=a0+B(x,x). The parallelogram identity also identifies this B with (A(x+y)-A(x-y))/4, since the baseline cancels.

For uniqueness, if C is another symmetric bilinear form with A(x)=a0+C(x,x), then C and B have equal diagonals at x, y, and x+y. Expanding at x+y and using symmetry gives 2C(x,y)=2B(x,y), hence C=B. Conversely, substitute A(x)=a0+B(x,x) and expand both rotated diagonals by bilinearity. The mixed terms cancel and their sum is (c squared+s squared)(B(x,x)+B(y,y)), which equals B(x,x)+B(y,y). The two baseline terms occur on both sides.

This application has no marker U and does not invoke Balance or raw_real_polar as an extra premise. It assumes no norm, topology, continuity, dimension bound, scalar homogeneity or nondegeneracy. The zero vector space, every nonnegative constant A, the zero form and forms with a radical are included; uniqueness concerns symmetric positive semidefinite forms. It is a consequence of the existing quadratic and real-polar constructions, with no claim of mathematical novelty or physical realization. The fixed-angle Hamel construction and the later calibration of a physical source are separate assertions.

## References

- Truth anchor: `D5/S3/QuadraticForms/RealThreePathPolar.Balance`
- Truth anchor: `D5/S3/QuadraticForms/RealThreePathPolar.raw_real_polar`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](ParallelogramConstruction.md)
- Dependency: [D5/S3/QuadraticForms/ThreeWayPositiveKernel](ThreeWayPositiveKernel.md)
