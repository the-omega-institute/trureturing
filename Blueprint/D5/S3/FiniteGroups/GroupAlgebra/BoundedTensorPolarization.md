# Exactness inside the polynomial rectangle

## Abstract

Denominator-free polarization gives the exact bounded polynomial tensor sequence and its equivariant section.

The polynomial model comes from Elmer and Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12). Simultaneous translation on two polynomial variables is the primal form of the diagonal tensor action. The denominator-free coefficient identities concern formal polynomials over a commutative ring R; they require neither a field nor a characteristic assumption.

**Theorem 1.1 (A section before division).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.diagonal_polarization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.diagonal_polarization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write P_N for the R-module of polynomials of degree at most N, with basis 1,z,...,z^N. For natural N,n and 0<=k<=N define Delta_(N,n)(z^k) to be the coefficient of t^n in (t+1)^(N-k)(t*z1+z2)^k. Extend by R-linearity to a map from P_N to R[z1,z2]. This construction uses no division, including when n>N or N=0.

Diagonal substitution mu(F)=F(z,z) gives mu Delta_(N,n)(f)=choose(N,n)*f for every f in P_N. Indeed the generating polynomial becomes (t+1)^N*z^k on the diagonal. For N=n+m, the coefficient formula has terms choose(N-k,n-r)*choose(k,r)*z1^r*z2^(k-r), only for 0<=r<=k with r<=n and k-r<=m. The rectangular bounds follow from vanishing of the out-of-range binomial coefficients; natural subtraction alone would not justify them.

For every c in R, simultaneous substitution z1->z1+c, z2->z2+c takes Delta_(N,n)(z^k) to the sum over 0<=j<=k of choose(k,j)*c^(k-j)*Delta_(N,n)(z^j). Thus polarization intertwines the entire translation action, with all lower terms. Over a field, division by the scalar choose(N,n) supplies a translation-equivariant section when that scalar is nonzero. The denominator-free identity itself remains valid when the scalar vanishes.

**Theorem 1.2 (The invariant difference has no kernel).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_mul_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_mul_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every commutative ring R, multiplication by z1-z2 on R[z1,z2] is injective. Regard the ring as (R[z2])[z1]: the polynomial z1-z2 is monic in z1, so multiplication by it is injective even if R has zero divisors, and also for the zero ring. Under simultaneous translation the difference is unchanged. Multiplication by this difference therefore gives the injective, translation-equivariant map between the smaller and larger polynomial rectangles used in the tensor splitting.

Let P_n be the polynomials of degree at most n. Sending z^r tensor z^s to z1^r*z2^s identifies P_n tensor P_m with its actual rectangular subspace in the two-variable polynomial ring. The first factor is the z1 variable. The translation model is that of Elmer and Kadr, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12).

**Theorem 1.3 (The kernel is the smaller rectangle).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.differenceTensor_range`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.differenceTensor_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any field K and for all natural n,m, let d:P_n tensor P_m -> P_(n+1) tensor P_(m+1) send z^r tensor z^s to z^(r+1) tensor z^s - z^r tensor z^(s+1). Let mu:P_(n+1) tensor P_(m+1) -> P_(n+m+2) be multiplication. Then range(d)=ker(mu). Both maps intertwine every simultaneous translation.

The polynomial realization takes d to multiplication by z1-z2, so d is injective. Diagonal restriction kills its image. Multiplication is surjective: each z^k can be lifted to z^min(k,n+1) tensor z^(k-min(k,n+1)). This lift proves surjectivity without asserting that it is equivariant. The dimension of ker(mu) is (n+2)(m+2)-(n+m+3)=(n+1)(m+1), equal to the dimension of the injective image of d. This proves exactness within the finite rectangle. The cases n=0 or m=0 are included; P_0 is the one-dimensional constant module.

**Theorem 1.4 (Invert the binomial, preserve every translation).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.equivariant_section`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.equivariant_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a field K and any natural n,m, suppose c=choose(n+m,n), regarded in K, is nonzero. There is a K-linear sigma:P_(n+m) -> P_n tensor P_m with mu sigma=id, and sigma intertwines translation by every a in K. No finiteness or positive-characteristic assumption on K is needed, and n=0 or m=0 is allowed.

The coefficient polarization for N=n+m lies in this bounded tensor rectangle. It obeys mu Delta=c*id and intertwines simultaneous translation. Set sigma=c^(-1)*Delta. Thus a nonzero binomial gives a section of the actual polynomial multiplication map. If c=0, this construction still has mu Delta=0 and supplies no right inverse; the converse obstruction for the relative stable relation comes from traces, rather than from the failure of this construction alone.

**Definition 1.5 (The tensor of duals with its actual action).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.dualTensorEquiv`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.dualTensorEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let G be any group and rho,tau representations over K on finite-dimensional spaces A,B. There is an equivariant linear equivalence A^* tensor B^* -> (A tensor B)^*, sending lambda tensor eta to the functional x tensor y -> eta(y)*lambda(x). The source has the tensor of the two contragredient actions; the target has the contragredient of the tensor action. Both sides evaluate the group element through its inverse, so the equivalence requires no change of the polynomial action. Zero-dimensional A or B is included.

Transposing a G-map F:A->B reverses its direction: F^*:B^*->A^* remains equivariant because the intertwining relation holds at g^(-1) as well as at g. This lets polynomial multiplication, its equivariant section and the difference map pass to the original V_d spaces.

**Theorem 1.6 (Recover the kernel component from an actual section).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_kernelRetraction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_kernelRetraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural n,m put B=P_(n+1) tensor P_(m+1), A=P_(n+m+2), C=P_n tensor P_m. Let mu:B->A be multiplication and d:C->B multiplication by z1-z2 in the polynomial realization. Given any K-linear section sigma:A->B with mu sigma=id, define h:B->C by inverting d on its image and applying it to id_B-sigma mu. Exactness makes this definition meaningful, and the identity is d h=id_B-sigma mu. Only a linear section is assumed in this statement.

If sigma intertwines translations, the injectivity and equivariance of d force h to intertwine them as well. Injectivity also gives h d=id_C and h sigma=0. Transposition therefore supplies an actual direct complement on the duals. Under the tensor-dual equivalences, the complement inclusion is the positive map h^*, and mu^* sigma^*+h^* d^*=id. For maps f=mu^* and g=sigma^*, the relative inverse error is f g-id=-h^* d^*. The negative sign belongs to that error, rather than to the complement inclusion.

The equivariant section used here is choose(n+m+2,n+1)^(-1) times bounded polarization, under the hypothesis that this scalar is nonzero in K. The formulas work over arbitrary fields. Tensor factors V_0 are zero, and V_1 is the trivial one-dimensional tensor unit; when a one-step tensor splitting reaches dimension one, these actual zero and unit modules give its boundary case.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.diagonal_polarization`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.differenceTensor_range`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_kernelRetraction`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.difference_mul_injective`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.dualTensorEquiv`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization.equivariant_section`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample](ElmerKadrTensorCounterexample.md)
