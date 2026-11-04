# The original-group Hilbert representation

## Abstract

The original nonnegative three-way law on any additive group is equivalent to a complete minimal complex Hilbert representation, with a unique label-preserving complex-linear unitary between any two representations.

**Theorem 1.1 (Complete representation, converse and unique unitary).**

$$\forall (A : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(A\right)], \forall (U : \operatorname{AddMonoidHom}\left(A, A\right)), \forall (q : (A \to \mathbb{R})), (\forall (x : A), 0 \le \operatorname{q}\left(x\right)) \Rightarrow ((\forall (x : A), \forall (y : A), \operatorname{q}\left(x + y\right) + \operatorname{q}\left(x + \operatorname{U}\left(y\right)\right) + \operatorname{q}\left(x + \operatorname{U}\left(\operatorname{U}\left(y\right)\right)\right) = 3 \cdot \operatorname{q}\left(x\right) + 3 \cdot \operatorname{q}\left(y\right)) \iff \operatorname{Nonempty}\left(\operatorname{HilbertRepresentation}\left(U, q\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{HilbertRepresentation}\left(U, q\right)\right) \Rightarrow (\forall (x : A), \forall (y : A), \operatorname{q}\left(x + y\right) + \operatorname{q}\left(x + \operatorname{U}\left(y\right)\right) + \operatorname{q}\left(x + \operatorname{U}\left(\operatorname{U}\left(y\right)\right)\right) = 3 \cdot \operatorname{q}\left(x\right) + 3 \cdot \operatorname{q}\left(y\right))) \land (\forall (R : \operatorname{HilbertRepresentation}\left(U, q\right)), \forall (S : \operatorname{HilbertRepresentation}\left(U, q\right)), \exists! e : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{H}\left(R\right), \operatorname{H}\left(S\right)\right), \forall (x : A), \operatorname{e}\left(\operatorname{label}\left(R, x\right)\right) = \operatorname{label}\left(S, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ThreeWayPositiveKernel.three_way_hilbert_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is an arbitrary additive commutative group, U an arbitrary additive endomorphism, and q an arbitrary finite real-valued nonnegative function. The balance law is universal in both original labels. There is no topology, rational or real scalar action, divisibility, faithfulness, invertibility, finite dimension or bounded iteration depth on A.

Rep(U,q) denotes HilbertRepresentation U q: it packages a complex inner-product space H with a normed additive group and completeness, an additive label map iota:A to H, and exactly the following conditions. The converse accepts any carrier universe, and the two carrier universes in uniqueness are independent; the constructed carrier has the original label universe. A linear isometry equivalence over the complex numbers is the unitary appearing in the statement.

$$
\forall (A : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(A\right)], \forall (U : \operatorname{AddMonoidHom}\left(A, A\right)), \forall (q : (A \to \mathbb{R})), \forall (R : \operatorname{HilbertRepresentation}\left(U, q\right)), (\operatorname{CompleteSpace}\left(\operatorname{H}\left(R\right)\right)) \land (\operatorname{NormedAddCommGroup}\left(\operatorname{H}\left(R\right)\right)) \land (\operatorname{InnerProductSpace}\left(\mathbb{C}, \operatorname{H}\left(R\right)\right)) \land (\forall (x : A), \forall (y : A), \operatorname{label}\left(R, x + y\right) = \operatorname{label}\left(R, x\right) + \operatorname{label}\left(R, y\right)) \land (\forall (x : A), \operatorname{q}\left(x\right) = \operatorname{norm}\left(\operatorname{label}\left(R, x\right)\right)^{2}) \land (\forall (x : A), \operatorname{label}\left(R, \operatorname{U}\left(x\right)\right) = omega \cdot \operatorname{label}\left(R, x\right)) \land (\operatorname{topologicalClosure}\left(\operatorname{span}\left(\mathbb{C}, \operatorname{range}\left(\operatorname{label}\left(R\right)\right)\right)\right) = top)
$$

The phase is omega=-1/2+i sqrt(3)/2. ThreeWayBalance.three_way_quadratic_structure is applied directly to the original A to obtain an integer quadratic map Q. Half its existing polar bilinear companion is the symmetric pairing b(x,y)=(q(x+y)-q(x-y))/4, with b(x,x)=q(x). The original U-invariance and invisible orbit sums imply b(Ux,Uy)=b(x,y) and b(Ux,y)+b(x,Uy)=-b(x,y).

The structural theorem also gives q(z+Dx)=q(z) for every original z,x, where Dx=x+Ux+U squared x. Its parameters are exactly the same A,U,q and the same universal balance hypothesis as in this representation theorem. This full-background identity concerns readouts; it does not impose Dx=0 on A.

More explicitly, b is the integer bilinear map (1/2) times Q.polarBilin. Linearity of this existing polar companion gives additivity in each slot, symmetry follows by exchanging x,y, and QuadraticMap.polar_self gives b(x,x)=q(x), hence nonnegativity on the diagonal. For any other symmetric biadditive real pairing c with c(x,x)=q(x), expansion of c(x+y,x+y) gives q(x+y)=q(x)+2c(x,y)+q(y). Thus c(x,y)=(q(x+y)-q(x)-q(y))/2, which equals the displayed polarization formula by the parallelogram law. The diagonal q therefore determines this pairing uniquely, including degenerate and zero cases; no division in A is used.

Nonnegative integer Gram sums are values of b on actual finite integer sums in A. IsLocalization.exist_integer_multiples_of_finite clears rational coefficients; DenseRange.piMap applied to Rat.denseRange_cast and closedness of a finite polynomial inequality then supplies arbitrary real coefficients. Continuity belongs only to the numerical coefficient vector, not to A.

$$
\forall (A : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(A\right)], \forall (U : \operatorname{AddMonoidHom}\left(A, A\right)), \forall (q : (A \to \mathbb{R})), \forall (x : A), \forall (y : A), \operatorname{complexGram}\left(U, q, x, y\right) = \frac{\operatorname{q}\left(x + y\right) - \operatorname{q}\left(x - y\right)}{4} + i \cdot \frac{\frac{\operatorname{q}\left(x + y\right) - \operatorname{q}\left(x - y\right)}{4} + 2 \cdot \frac{\operatorname{q}\left(\operatorname{U}\left(x\right) + y\right) - \operatorname{q}\left(\operatorname{U}\left(x\right) - y\right)}{4}}{\operatorname{sqrt}\left(3\right)}
$$

The complex Gram K uses the convention conjugate-linear in its first label. For complex coefficients z, its quadratic sum is the real Gram quadratic sum on the same labels x and Ux with coefficients Re(z)+Im(z)/sqrt(3) and 2Im(z)/sqrt(3). This proves positivity for every finite support, including the zero kernel. The covariance is K(Ux,y)=conj(omega)K(x,y).

The scalar kernel is lifted to K(x,y) times the identity continuous linear map on the complex numbers. RKHS.posSemidef_iff_re_sum_kernel' supplies the exact interface, RKHS.OfKernel supplies the completed carrier, and RKHS.OfKernel.kernel_ofKernel recovers the original entries. Kernel vectors at value 1 define the additive labels. Their diagonal inner product gives q, covariance gives omega, and RKHS.kerFun_dense gives the closed complex span. No independent completion framework is constructed.

For any two complete minimal representations, real polarization and the specified phase force their full complex Gram to equal K. Each embeds into functions on the original labels by v mapped to the inner products of each label with v; density makes this map injective. The resulting reproducing kernel spaces have identical kernels, so RKHS.equiv and RKHS.equiv_kerFun give a label-preserving complex-linear isometry equivalence. Density of the original label span proves that any other such equivalence agrees everywhere. No nontriviality assumption excludes the zero representation.

Conversely, the norm-square identity in any representation gives the balance law: omega has modulus one and 1+omega+omega squared is zero, so all mixed inner-product terms cancel. This establishes both directions under the original additive-group hypotheses. The construction is mathematical completion and scalar extension; it asserts no native physical real-scalar operation or process implementation.

## References

- Truth anchor: `D5/S3/QuadraticForms/ThreeWayPositiveKernel.three_way_hilbert_characterization`
- Dependency: [D5/S3/QuadraticForms/ThreeWayBalance](ThreeWayBalance.md)
