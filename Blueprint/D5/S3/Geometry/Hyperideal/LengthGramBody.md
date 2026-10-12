# One shared body from the actual length Gram matrix

## Abstract

The common six-length cut body has a Lorentz and upper-half-space coordinate realization.

Let l be six positive real lengths in the order (01,02,03,23,13,12). The symmetric matrix G has diagonal entries one and off-diagonal entries minus cosh of the corresponding length. The set C consists of nonnegative four-coordinate vectors whose coordinates sum to one and whose four G-row values are nonpositive. Write q(v)=v-transpose G v, r(v)=v/sqrt(-q(v)), and b=(1/4,1/4,1/4,1/4). R6 and R4 denote real coordinate spaces. B is the Lorentz form with signs (+,+,+,-). The function phi01 is the original six-variable cosine formula applied to cosh(l). For a future unit timelike y, Psi(y) has horizontal coordinate (y0+i*y1)/(y3-y2) and height 1/(y3-y2). H3 denotes the repository's HyperbolicThreeSpace with its actual metric topology.

**Theorem 1.1 (Compactness, explicit frame and shared coordinate map).**

$$\forall l \in R6,\; \left(\forall k \in Fin\left(6\right),\; 0 < l\left(k\right)\right) \Rightarrow \left(IsCompact\left(C\left(l\right)\right) \land \left(b \in C\left(l\right) \land \left(\left(\forall i \in Fin\left(4\right),\; Gb\left(l, i\right) < 0\right) \land \left(\left(\forall v \in R4,\; v \in C\left(l\right) \Rightarrow q\left(l, v\right) < 0\right) \land \left(ContinuousOn\left(r\left(l\right), C\left(l\right)\right) \land \left(InjOn\left(r\left(l\right), C\left(l\right)\right) \land \left(IsCompact\left(image\left(r\left(l\right), C\left(l\right)\right)\right) \land \left(Nonempty\left(image\left(r\left(l\right), C\left(l\right)\right)\right) \land \left(\left(\forall v \in R4,\; v \in C\left(l\right) \Rightarrow q\left(l, r\left(l, v\right)\right) = -1\right) \land \left(\left(-1 < phi01\left(l\right) \land phi01\left(l\right) < 1\right) \Rightarrow \left(\exists m \in Matrix4,\; \left(\forall i \in Fin\left(4\right),\; \forall j \in Fin\left(4\right),\; B\left(row\left(m, i\right), row\left(m, j\right)\right) = G\left(l, i, j\right)\right) \land \left(0 < det\left(m\right) \land \left(det\left(G\left(l\right)\right) < 0 \land \left(\exists f \in Maps\left(C\left(l\right), H3\right),\; Continuous\left(f\right) \land \left(Injective\left(f\right) \land \left(IsCompact\left(range\left(f\right)\right) \land \left(Nonempty\left(range\left(f\right)\right) \land \left(\forall v \in C\left(l\right),\; \exists y \in R4,\; y = vecMul\left(r\left(l, v\right), m\right) \land \left(B\left(y, y\right) = -1 \land \left(0 < coord\left(y, 3\right) \land coordinates\left(f\left(v\right)\right) = Psi\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The barycenter strictly satisfies every cut. A cut equality at a positive coordinate forces that coordinate to exceed one half. If q vanished, every positive coordinate would require a cut equality. Two positive coordinates cannot both exceed one half, while a singleton support violates its own cut. Thus q is strictly negative throughout the same C.

The positive square-root denominator makes r continuous. The sum of the image coordinates recovers its reciprocal scale, so r is injective. Its image is compact and nonempty, and the quadratic value there equals minus one.

The strict condition on phi01 makes the final square root in the explicit four-vector frame positive. The frame's Lorentz Gram is exactly G and its determinant is positive. Congruence with diag(1,1,1,-1) gives det(G)<0. Every point of the same radial body is future unit timelike. Its positive denominator y3-y2 defines Psi throughout C. The coordinate inverse proves injectivity, and the existing coordinate homeomorphism proves continuity into actual H3.

This closes the shared compact coordinate-body and frame step of the original six-length construction. It does not yet assert three-dimensional interior, complete triangular/hexagonal incidence, geodesic intervals, prescribed edge distances, dihedral angles or relabeling isometries. Those obligations retain the original all-six strict source cosine domain; one strict condition suffices for this frame step.

For the original volume calculation, retain all six positive lengths and all six strict source cosines, and fix any original witnesses M and f satisfying the displayed frame and radial-coordinate equations. Use EuclideanSpace Real (Fin 3) with its L2 norm and canonical three-dimensional Haar volume. Set A(u)=(1-u0-u1-u2,u0,u1,u2), D=A inverse-image C, X=A(u) times M, s=sqrt(-q(A(u))) and d=X3-X2. The sum-one condition on C proves A(D)=C: the inverse chart is P(v)=(v1,v2,v3). The same future unit timelike radial vector is Y=X/s, so s>0 and d=s*(Y3-Y2)>0 on all of D. Consequently the actual coordinates of f(A(u)) are (F0+i*F1,F2), where F(u)=(X0/d,X1/d,s/d). This identifies the literal original map, including all cut-boundary points; no alternate frame or body is selected.

The Frechet derivative rules give the ambient derivative of this F where q(A(u))<0 and d is nonzero. For h in Real3, put v=(-h0-h1-h2,h0,h1,h2), w=v times M and delta=w3-w2. Then Ds[h]=-B(X,w)/s, and the derivative is DF[h]=(w0/d-X0*delta/d^2, w1/d-X1*delta/d^2, -B(X,w)/(s*d)-s*delta/d^2). This is an actual derivative of the coordinate function. Its restriction supplies a derivative within D even where a cut equality is active; boundary smoothness is unnecessary.

The signed determinant follows by homogeneous coordinates. Let H(X)=(X0,X1,s,X3-X2). Its four-dimensional derivative has determinant d/s and sends X to H(X). The matrix with rows A and the three coordinate derivatives of A has determinant one, so the matrix with rows X and the three derivatives of X has determinant det(M). Applying DH gives a determinant det(M)*d/s. Subtract delta/d times the first row from each derivative row. The last column becomes (d,0,0,0), while each remaining derivative row is d times the corresponding derivative row of F. Expansion in the last column gives -d^4*det(DF). Thus det(DF)=-det(M)/(s*d^3), with the sign fixed by row-vector action and output order (horizontal real, horizontal imaginary, height).

$$
det\left(DF\left(u\right)\right) = \frac{-det\left(M\right)}{s \cdot d^{3}}
$$

The same frame congruence G=M*diag(1,1,1,-1)*transpose(M) gives det(G)=-det(M)^2 and sqrt(-det(G))=abs(det(M)). Since F2=s/d and s,d are positive, cancellation yields the exact weighted Jacobian below. The three-dimensional determinant uses the standard L2 orthonormal coordinates; there is no induced four-dimensional simplex measure or extra hyperplane factor.

$$
\left(F_{2}\right)^{-3} \cdot abs\left(det\left(DF\left(u\right)\right)\right) = \frac{sqrt\left(-det\left(G\right)\right)}{\left(0 - q\left(A\left(u\right)\right)\right)^{2}}
$$

Let N take the native coordinates of a point in H3 to the real triple (horizontal real, horizontal imaginary, height). Then F(D)=N(range(f)) for the same f. Packing a real triple back into (Complex,Real) is injective; the original injectivity of f and the inverse affine chart therefore give injectivity of F on D. The projection P sends the compact C onto D, so D is compact and measurable. The original coordinate homeomorphism makes N continuous, and N(range(f)) is compact and measurable in Real3. Thus the image correspondence and the domain conditions needed by measurable-set change of variables apply to the original body including its entire boundary.

These identities give the actual change-of-variables Jacobian with the original frame equations. The mass application below combines measurable-set change of variables on the actual image with HyperbolicNormalizedDensity.raw_native_density and its existing exact L2 orthonormal-cube Haar calibration. Native mass equality, positive finite native mass and witness independence are not conclusions of the Jacobian calculation alone. The flat-boundary limit, face and angle identification, Schlaefli variation and co-volume conclusions remain separate; zero lengths are excluded.

For this mass application, keep all six original positive lengths in the order (01,02,03,23,13,12) and both strict inequalities for each of the six original source cosines. Let M be any original frame with B(row_i(M),row_j(M))=G_ij and det(M)>0, and let f be any original continuous injective map from the same C into native H3 satisfying, at every v in C, Y=r(v) times M, B(Y,Y)=-1, Y3>0 and coordinates(f(v))=Psi(Y). Retain the same f, native hyperbolic metric and full closed cut body. In the affine chart A and domain D above, define rho_l and I_l by the following formulas; integralOn denotes the real set integral against the canonical L2 three-dimensional volume volume3.

$$
\left(rho_{l}\right)\left(u\right) = \frac{sqrt\left(-det\left(G\right)\right)}{\left(0 - q\left(A\left(u\right)\right)\right)^{2}}
$$

$$
I_{l} = integralOn\left(rho_{l}, D, volume3\right)
$$

The density is integrable and I_l is strictly positive. LengthGramBody.shared_radial_body gives q(A(u))<0 throughout D, including its boundary. The checked original Gram-frame determinant identity gives det(G)=-det(M)^2<0 from det(M)>0. Compactness follows from D=P(C), and the strictly cut barycenter has an open affine neighborhood in D, giving nonempty three-dimensional interior. Thus rho_l is continuous and strictly positive on the compact D. Compact-domain integrability and the positive volume of its positive support give the assertions below; no determinant-sign or integral-positivity conclusion is added as a hypothesis.

$$
IntegrableOn\left(rho_{l}, D, volume3\right) \land 0 < I_{l}
$$

Use the existing HyperbolicNormalizedDensity normalization convention. In Amb=WithLp 2 (Complex times Real), Q is the parallelepiped of the standard real orthonormal basis, and c3 is its raw ambient Hausdorff three-mass. The product orthonormal basis proves real dimension three. Haar uniqueness and the unit canonical volume of an orthonormal parallelepiped identify ambient Hausdorff measure with c3 times ambient volume. The compact Q has nonempty interior, so c3 is strictly positive and finite; these facts are derived.

$$
Amb = WithLp\left(2, Product\left(Complex, Real\right)\right)
$$

$$
Q = parallelepiped\left(toBasis\left(stdOrthonormalBasis\left(Real, Amb\right)\right)\right)
$$

$$
c3 = mass\left(hausdorffMeasure\left(3, Amb\right), Q\right)
$$

$$
0 < c3 \land \left(c3 < \infty \land hausdorffMeasure\left(3, Amb\right) = smul\left(c3, volume\left(Amb\right)\right)\right)
$$

The literal packing z maps to WithLp.toLp 2 (Complex.mk(z0,z1),z2). It is exactly the real linear isometry obtained from the product orthonormal basis in that coordinate order, preserving canonical volume and Hausdorff measure. On the positive-height coordinate subtype its inverse unpack has unpack(x)2=height(x), and unpack(coordinatesEquiv(p))=N(p). Applying the existing raw_native_density to the same set range(f), then transporting its withDensity lower integral through this measurable isometric unpack, gives the raw mass formula below. The restriction to range(unpack) disappears on the actual image contained in that range. Here weight(z)=ofReal(z2^(-3)), lowerIntegral denotes the extended nonnegative set integral, and rawNativeMeasure is Hausdorff three-measure for the original native H3 metric.

$$
mass\left(rawNativeMeasure, range\left(f\right)\right) = c3 \cdot lowerIntegral\left(weight, image\left(F, D\right), volume3\right)
$$

The sets D and F(D)=N(range(f)) are Borel because they are compact; range(f) itself is compact and Borel by continuity of the same original f. The previously checked literal map F is injective on D, has its ambient derivative at every point of D, and satisfies F2(u)^(-3)*abs(det(DF(u)))=rho_l(u). Its within-derivative therefore instantiates measurable-set change of variables on the full closed D, with no cut-equality or inactive-boundary point removed. Define ofRealDensity(u)=ofReal(rho_l(u)) and lowerGramIntegral_l as its lower integral over D. The weighted Jacobian equates the image lower integral with lowerGramIntegral_l; real integrability and nonnegativity identify it with ofReal(I_l).

$$
lowerGramIntegral_{l} = lowerIntegral\left(ofRealDensity, D, volume3\right)
$$

$$
lowerIntegral\left(weight, image\left(F, D\right), volume3\right) = lowerGramIntegral_{l}
$$

$$
lowerGramIntegral_{l} = ofReal\left(I_{l}\right)
$$

Set muNorm=c3 inverse smul rawNativeMeasure, exactly as in the existing normalization. Cancellation of the nonzero finite c3 yields the exact same-witness mass identities below. The toReal identity uses I_l>0. Consequently both normalized and raw native masses are strictly positive and finite.

$$
muNorm = smul\left(inv\left(c3\right), rawNativeMeasure\right)
$$

$$
mass\left(muNorm, range\left(f\right)\right) = lowerGramIntegral_{l} = ofReal\left(I_{l}\right)
$$

$$
toReal\left(mass\left(muNorm, range\left(f\right)\right)\right) = I_{l}
$$

$$
mass\left(rawNativeMeasure, range\left(f\right)\right) = c3 \cdot ofReal\left(I_{l}\right)
$$

$$
0 < mass\left(muNorm, range\left(f\right)\right) \land \left(mass\left(muNorm, range\left(f\right)\right) < \infty \land \left(0 < mass\left(rawNativeMeasure, range\left(f\right)\right) \land mass\left(rawNativeMeasure, range\left(f\right)\right) < \infty\right)\right)
$$

For any two admissible original witness pairs (M,f) and (Mprime,fprime) with the same length vector l, the normalized masses agree because each equals ofReal(I_l); the raw masses agree because each equals c3*ofReal(I_l). The conclusion is equality of masses and asserts no equality of the two ranges. This application uses the original literal Jacobian and image identities, raw_native_density, Hausdorff-Haar calibration, measurable-set change of variables and real/lower-integral conversion. It closes the native mass application, while flat-boundary limits, actual face and angle identification, Schlaefli variation, co-volume and full CFMP completion remain separate.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramBody.shared_radial_body`
- Dependency: [D5/S3/Geometry/HyperbolicTopology](../HyperbolicTopology.md)
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
