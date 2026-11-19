# The generated JB complexification in the original norm

## Abstract

The original-norm complexification of a single-generated JB algebra supplies an ambient quadratic-invertibility bridge and a proof that every quadratic representation preserves the original square cone in an arbitrary complete real six-law JB algebra, including the zero algebra.

Let R be a real normed commutative unital algebra, with its specified norm and product. SquareLaws means norm(r^2)=norm(r)^2 and norm(r^2)<=norm(r^2+s^2) for every r,s. No order, positivity representation, spectral calculus or nonzero hypothesis is assumed. Let Z=QuadraticAlgebra(R,-1,0). Thus (r+is)(v+iw)=(rv-sw)+i(rw+sv), conjugation is r-is, and the unit is 1+i0. Define N(r+is)=sqrt(norm(r^2+s^2)).

**Theorem 1.1 (The actual norm axioms).**

$$\forall R \in RealNormedCommutativeUnitalAlgebras,\; \forall L \in SquareLaws\left(R\right),\; NormedSpaceCore\left(Real, Complexification\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.normCore` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

Square monotonicity and the square norm law give norm(r)<=N(r+is) and norm(s)<=N(r+is), proving definiteness. The identity (rv+sw)^2+(rw-sv)^2=(r^2+s^2)(v^2+w^2), together with product norm domination, gives norm(rv+sw)<=N(r+is)N(v+iw). Expanding the square-sum of (r+v)+i(s+w) and applying the norm triangle inequality gives N(z+w)^2<=(N(z)+N(w))^2. Nonnegativity yields the required triangle inequality. Real scalar homogeneity follows from the square-sum formula. The resulting metric is defined by this N.

**Theorem 1.2 (Submultiplicativity).**

$$\forall R \in RealNormedCommutativeUnitalAlgebras,\; \forall z \in Complexification\left(R\right),\; \forall w \in Complexification\left(R\right),\; squareNorm\left(multiply\left(z, w\right)\right) \le multiply\left(squareNorm\left(z\right), squareNorm\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.squareNorm_mul_le` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

The square-sum of zw equals (r^2+s^2)(v^2+w^2). Product norm domination followed by the nonnegative square-root comparison gives N(zw)<=N(z)N(w). This step supplies the normed commutative ring structure.

**Theorem 1.3 (Complex scalar homogeneity).**

$$\forall R \in RealNormedCommutativeUnitalAlgebras,\; \forall c \in Complex,\; \forall z \in Complexification\left(R\right),\; squareNorm\left(smul\left(c, z\right)\right) = multiply\left(norm\left(c\right), squareNorm\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.squareNorm_complex_smul` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

The scalar homomorphism sends c to (algebraMap(Re(c)),algebraMap(Im(c))). The square-sum of cz is (Re(c)^2+Im(c)^2) times that of z, giving N(cz)=norm(c)N(z). Conjugation respects this action. Also star(z)z=(r^2+s^2)+i0, so the real square norm law gives N(star(z)z)=N(z)^2.

**Definition 1.4 (Completeness and the complex C* algebra).**

$$\forall R \in RealNormedCommutativeUnitalAlgebras,\; \forall L \in SquareLaws\left(R\right),\; \forall B \in CompleteSpace\left(R\right),\; CommCStarAlgebra\left(Complexification\left(R\right)\right)$$

*Formalization.* `D5/S3/Topology/JBComplexification.complexCommCStarAlgebra` (`✓ std3`).

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

The coordinate equivalence z -> (Re(z),Im(z)) has norm at most N(z). Conversely N(z)<=norm(Re(z))+norm(Im(z))<=2 max(norm(Re(z)),norm(Im(z))). These two bounds make the equivalence a uniform embedding onto the complete product R x R. Completeness transfers to the metric defined by N. All the preceding structures therefore combine into an actual commutative unital complex C* Banach algebra. In the zero algebra the unit and norm are zero, and the same construction and proofs apply.

**Theorem 1.5 (The original real algebra and the selfadjoint part).**

$$\forall R \in RealNormedCommutativeUnitalAlgebras,\; \forall L \in SquareLaws\left(R\right),\; Isometry\left(realEquiv\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.realEquiv_isometry` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

The subalgebra realPart consists exactly of elements fixed by conjugation. Such an element has imaginary component zero: -s=s implies 2s=0, and real scalar cancellation gives s=0, also in the zero space. The map realEquiv:r -> r+i0 is a real algebra isomorphism onto this subalgebra, with inverse the real component. Its norm is sqrt(norm(r^2))=norm(r). The same maps form the real linear isometric equivalence realIsometry.

**Theorem 1.6 (Ambient quadratic bijectivity forces a generated inverse).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall a \in X,\; Bijective\left(U\left(a\right)\right) \Rightarrow \left(\exists b \in X,\; mem\left(b, generated\left(a\right)\right) \land S\left(a, b\right) = u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.generated_inverse_of_quadratic_bijective` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

Let X be any complete real normed vector space with the original six-law Data(X,S,u), including the zero space. If U(a,v)=2 S(a,S(a,v))-S(S(a,a),v) is bijective on X, then there is b in the original closed algebra generated by a with S(a,b)=u. The Banach inverse theorem first gives norm(v)<=M norm(U(a,v)). Restricting to the generated algebra turns U(a) into multiplication by a^2.

The nonvanishing step uses an actual continuous-function construction. If multiplication by c is bounded below in a complete associative real JB algebra and a character vanishes on c, set epsilon=1/(M+1) and f(psi)=1/(abs(g(c)(psi))+epsilon). The inverse Gelfand transform of f is selfadjoint, so it is the image of an original real element r. At the zero character norm(r)>=M+1, while the pointwise product estimate gives norm(cr)<=1. The lower bound would give norm(r)<=M, a contradiction. Thus c is a unit in the complexification. The real part of its inverse is an inverse in the original real algebra. Applying this to c=a^2 and multiplying once by a returns the asserted b.

**Theorem 1.7 (Every original quadratic representation preserves squares).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall a \in X,\; \forall x \in X,\; \exists y \in X,\; U\left(a, S\left(x, x\right)\right) = S\left(y, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBComplexification.quadratic_preserves_squares` (`✓ std3`). ∎

*Citation.* Harald Hanche-Olsen; Erling Størmer (1984). *Jordan Operator Algebras*. URL: <https://hanche.folk.ntnu.no/joa/joa-m.pdf>.

*Commentary.*

For every a,x in the same arbitrary complete real raw Data(X,S,u), there is y in that original X such that U(a,S(x,x))=S(y,y). Here U(a,z)=2 S(a,S(a,z))-S(S(a,a),z). The product, norm, unit and square cone are the specified original ones. No finite-dimensional, special, JC, ambient operator, supplied order or supplied spectral assumption is made. The proof includes the zero algebra without a nonzero premise.

First, transfer the pointwise real square-root construction through the actual complexification and Gelfand transform. In the original carrier, p is a square exactly when norm(p-norm(p)u)<=norm(p). In one direction use the algebra generated by a square root; in the other use the algebra generated by p itself. This characterizes the original square cone as a closed set. If p is a square and U(p) is bijective, the generated inverse excludes zero character values. Compactness then gives norm(p-(norm(p)+1)u)<norm(p)+1. The strict gap and the norm triangle inequality give a whole original-norm neighborhood of squares around p.

For positive epsilon,delta, connect a=x^2+epsilon u to u by a(t)=(1-t)a+t u and put c(t)=U(a(t),y^2+delta u). Every a(t) and y^2+delta u is a positive shift of a square. Their ambient quadratic maps are bijective by positive_shift_quadratic_bijective. The fundamental identity makes U(c(t)) bijective throughout the interval. The times at which c(t) is a square form a closed and open subset of the connected interval, and contain t=1. Thus c(0) is a square. Closedness and a positive-parameter limit give square-cone preservation for every square parameter a.

For arbitrary a, first take b=x^2+delta u. In the original algebra generated by x, real functional calculus gives c,d,t with c^2=b, cd=u and t^2=d. The fundamental identity makes U(c) injective and gives U(d)U(c)=I on the entire original carrier. Its specialization at the unit also gives (U(c)a)^2=U(c)U(a)b. The already proved square-parameter case applied to d=t^2 therefore shows U(a)b=U(d)((U(c)a)^2) is a square. Letting delta decrease to zero and using the closed original square cone proves the all-a, all-x statement.

This is the mature quadratic-positivity theorem of Hanche-Olsen and Stormer, Proposition 3.3.6. The proof uses original-norm complexification, the reciprocal-function nonvanishing argument, a connected path and positive approximation. It does not use a two-generator JC representation. The result supplies the U-positivity premise used in the original response application's Sections 183.5 and 183.9; it does not establish the remaining state, bidual, density, Peirce or response conclusions of Sections 183-184.

For raw Data(X,S,u) and a in X, Generated is the actual norm-closed real span of the powers of a in X, carrying the inherited norm and real vector-space operations. The generated_algebra theorem supplies closure and associativity, while Data supplies commutativity and the unit. Multiplication on Generated is exactly S and its unit is exactly u. The two SquareLaws and product norm domination restrict directly from Data. Closedness supplies completeness when X is complete. Thus GeneratedComplex is the construction above on that actual generated algebra; its norm is sqrt(norm(S(r,r)+S(s,s))) in the original ambient norm, and realEquiv is the required isometric real algebra identification. No completion, replacement norm, order-unit norm or ambient JC algebra is substituted.

Every nonzero z in a complete real normed space with raw Data(X,S,u) admits a continuous real-linear functional beta with beta(S(y,y))>=0 for every y in X, beta(u)=1, and abs(beta(z))=norm(z). To obtain it, use Generated(A,z), with its inherited norm. The nonzero element z makes this generated algebra nontrivial. Compactness of its complex character space and real_gelfand_norm select a character phi with abs(phi(z))=norm(z). real_character_value makes phi real on every real element, and real_character_scalar gives its value on t u. Its real restriction is a real-linear contraction with value one on u. The real Hahn-Banach theorem exists_extension_norm_eq extends this functional to X without increasing its norm and preserves both u and z.

Positivity of this extension follows from the original square geometry. For p=S(y,y), square_iff_center gives norm(p-norm(p)u)<=norm(p). Contractivity and beta(u)=1 imply abs(beta(p)-norm(p))<=norm(p), hence beta(p)>=0. Thus positivity holds on the actual square cone in X, although the character was chosen only in the algebra generated by z. No ambient associative representation, supplied state, supplied cone, order-unit-norm identification or finite-spectrum assumption is needed. The nonzero argument supplies local nontriviality; the statement makes no state-existence assertion for the zero algebra.

The complexification is the construction in Hanche-Olsen and Stormer, Jordan Operator Algebras, Section 3.2.2, pages 78-79. The generated-inverse implication belongs to the spectral and quadratic-invertibility correspondence of Sections 3.2.8-3.2.11; quadratic positivity is Proposition 3.3.6. These are known mathematical results. No literature novelty or physical ontology claim is made.

## References

- Truth anchor: `D5/S3/Topology/JBComplexification.complexCommCStarAlgebra`
- Truth anchor: `D5/S3/Topology/JBComplexification.generated_inverse_of_quadratic_bijective`
- Truth anchor: `D5/S3/Topology/JBComplexification.normCore`
- Truth anchor: `D5/S3/Topology/JBComplexification.quadratic_preserves_squares`
- Truth anchor: `D5/S3/Topology/JBComplexification.realEquiv_isometry`
- Truth anchor: `D5/S3/Topology/JBComplexification.squareNorm_complex_smul`
- Truth anchor: `D5/S3/Topology/JBComplexification.squareNorm_mul_le`
- Dependency: [D5/S3/Topology/JBAlgebra](JBAlgebra.md)
- Dependency: [D5/S3/Topology/JBPositiveShift](JBPositiveShift.md)
