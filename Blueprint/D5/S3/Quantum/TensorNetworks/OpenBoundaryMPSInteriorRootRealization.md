# From residual roots to actual interior ambiguity

## Abstract

A distinct common determinant root gives an actual finite uniform bond-two state with identical entire raw interior Q2 and a different full-state phase class; annular boundary and real transversality hypotheses give such a root conditionally.

**Definition 1.1 (The fixed sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Sector`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Sector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

A sector contains three arbitrary complex numbers lambda, mu and a. All trial operations keep this sector fixed.

**Definition 1.2 (Eigenvalue difference).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.delta`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

delta=mu-lambda.

**Definition 1.3 (First sector offset).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.alpha`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

alpha=lambda-a.

**Definition 1.4 (Second sector offset).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.beta`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.beta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

beta=mu-a.

**Definition 1.5 (Regular sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Regular`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Regular` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Regular means delta times alpha times beta is nonzero and normSq(1+conjugate(lambda) mu) is strictly positive. These are algebraic nonvanishing conditions, not positivity of an inverse.

**Definition 1.6 (Diagonal sector matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.B`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

B=diag(lambda,mu).

**Definition 1.7 (Trial core matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.G`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

G(z) has rows (1,z) and (alpha,beta z). Its determinant is delta z.

**Definition 1.8 (The fixed intertwining matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.C`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.C` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

C has rows (a,1) and (-alpha beta,lambda+mu-a). The exact identity C G(z)=G(z) B holds.

**Definition 1.9 (Uniform binary core).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.core`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.core` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The two matrices are A0=G(z), A1=B G(z), at every site.

**Definition 1.10 (Fixed central pair factors).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.K`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In word order 00,01,10,11 the matrices are I,C,B,BC, and A_i A_j=K_ij G(z)^2.

**Definition 1.11 (Algebraic diagonal inverse).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalInverse`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Entry (i,j) is divided by 1+b_i conjugate(b_j), where b=(lambda,mu). Regularity makes every divisor nonzero.

**Definition 1.12 (Algebraic adjoint diagonal inverse).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalStarInverse`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalStarInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Entry (i,j) is divided by 1+conjugate(b_i)b_j. Its order in inverseDualTransfer is essential.

**Definition 1.13 (Inverse transfer in its actual order).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseTransfer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

E_z inverse sends H to G(z) inverse times diagonalInverse(H) times G(z) inverse-adjoint. Both composition identities are proved. This algebraic inverse is not asserted to preserve positivity.

**Definition 1.14 (Inverse dual transfer in its actual order).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseDualTransfer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseDualTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

EStar_z inverse sends P to diagonalStarInverse(G(z) inverse-adjoint P G(z) inverse). Congruence occurs before the Schur inverse. Both composition identities are proved.

**Definition 1.15 (Fixed actual left environment).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.leftTarget`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.leftTarget` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

P=(EStar_z0)^p(l dagger l), for the original arbitrary actual left boundary l.

**Definition 1.16 (Fixed actual right environment).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.rightTarget`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.rightTarget` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

H=G(z0)^2 E_z0^q(r r dagger) (G(z0)^2) dagger. The central G square is included on both sides.

**Definition 1.17 (Trial left boundary Gram).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialLeft`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

X_p(zeta)=(inverseDualTransfer_zeta)^p(P), with P fixed.

**Definition 1.18 (Trial right boundary Gram).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialRight`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Y_q(zeta)=(inverseTransfer_zeta)^q(G(zeta) inverse-square H G(zeta) inverse-adjoint-square), with H fixed.

**Definition 1.19 (The explicit real residual).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.residual`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

f(zeta)=Re(det X_p(zeta))+I Re(det Y_q(zeta)). The map is real rather than holomorphic. Target P,H are fixed in all trial derivatives.

**Theorem 1.20 (Homogeneous iteration).**

$$\forall F \in Bond \to Bond,\; \left(\forall t \in Complex,\; \forall X \in Bond,\; F\left(smul\left(t, X\right)\right) = smul\left(t, F\left(X\right)\right)\right) \Rightarrow \left(\forall n \in Nat,\; \forall t \in Complex,\; \forall X \in Bond,\; iterate\left(F, n, smul\left(t, X\right)\right) = smul\left(t, iterate\left(F, n, X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.iterate_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Every complex-homogeneous map on Bond remains complex-homogeneous under every natural iterate, including zero. The original root-realization factorization and InteriorPolynomial's live right-boundary and Jacobian-scaling proofs directly consume this original helper.

**Theorem 1.21 (Homogeneous transfer).**

$$\forall A \in Fin\left(2\right) \to Bond,\; \forall t \in Complex,\; \forall X \in Bond,\; transfer\left(A, smul\left(t, X\right)\right) = smul\left(t, transfer\left(A, X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.transfer_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every binary pair of Bond matrices, every complex scalar and every Bond matrix, transfer commutes with scalar multiplication. The original root proof and InteriorPolynomial's actual right-target scaling use this declaration directly through iterate_smul; no positivity or nonzero-scalar hypothesis is added.

**Theorem 1.22 (Every distinct common root is actual).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall s \in Sector,\; \forall zo \in Complex,\; \forall l \in Fin\left(2\right) \to Complex,\; \forall r \in Fin\left(2\right) \to Complex,\; \left((((((1 \le p) \land (1 \le q)) \land (Regular\left(s\right))) \land (zo \neq 0)) \land (PosDef\left(leftTarget\left(s, zo, l, p\right)\right))) \land (PosDef\left(rightTarget\left(s, zo, r, q\right)\right))\right) \Rightarrow \left(\forall z \in Complex,\; \left((((z \neq 0) \land (z \neq zo)) \land (det\left(trialLeft\left(s, p, leftTarget\left(s, zo, l, p\right), z\right)\right) = 0)) \land (det\left(trialRight\left(s, q, rightTarget\left(s, zo, r, q\right), z\right)\right) = 0)\right) \Rightarrow \left(\exists phi \in Word\left(p + 2 + q\right) \to Complex,\; (((SetMember\left(phi, openBoundaryMPS\left(p + 2 + q\right)\right)) \land (phi \neq 0)) \land (rawInterior\left(p, 2, q, phi\right) = rawInterior\left(p, 2, q, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right))) \land (\neg (\exists eta \in Complex,\; (norm\left(eta\right) = 1) \land (phi = smul\left(eta, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right))))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.distinct_residual_root_actual_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, every regular sector, nonzero original z0, arbitrary complex l,r and positive definite actual P,H, any nonzero zeta distinct from z0 with both trial determinants zero gives a nonzero actual finite uniform bond-two competitor. It has identical complete unnormalized rawInterior p 2 q, at length (p+2)+q, and is not any unit complex scalar times the original full state. No canonical-chart or regularity hypothesis is imposed on the constructed boundaries.

**Theorem 1.23 (Conditional annular actual ambiguity).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall s \in Sector,\; \forall zo \in Complex,\; \forall l \in Fin\left(2\right) \to Complex,\; \forall r \in Fin\left(2\right) \to Complex,\; \left((((((1 \le p) \land (1 \le q)) \land (Regular\left(s\right))) \land (zo \neq 0)) \land (PosDef\left(leftTarget\left(s, zo, l, p\right)\right))) \land (PosDef\left(rightTarget\left(s, zo, r, q\right)\right))\right) \Rightarrow \left(\forall epsilon \in Real,\; \forall R \in Real,\; \forall L \in ContinuousLinearEquiv\left(Real, Complex, Complex\right),\; \left(((((0 < epsilon) \land (epsilon < norm\left(zo\right))) \land (norm\left(zo\right) < R)) \land (HasFDerivAt\left(residual\left(s, p, q, leftTarget\left(s, zo, l, p\right), rightTarget\left(s, zo, r, q\right)\right), toContinuousLinearMap\left(L\right), zo\right))) \land (\forall z \in Complex,\; \left(norm\left(z\right) = epsilon \lor norm\left(z\right) = R\right) \Rightarrow re\left(residual\left(s, p, q, leftTarget\left(s, zo, l, p\right), rightTarget\left(s, zo, r, q\right)\right)\left(z\right)\right) < 0)\right) \Rightarrow \left(\exists phi \in Word\left(p + 2 + q\right) \to Complex,\; (((SetMember\left(phi, openBoundaryMPS\left(p + 2 + q\right)\right)) \land (phi \neq 0)) \land (rawInterior\left(p, 2, q, phi\right) = rawInterior\left(p, 2, q, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right))) \land (\neg (\exists eta \in Complex,\; (norm\left(eta\right) = 1) \land (phi = smul\left(eta, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right))))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.annular_regular_root_actual_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Retain the same universal finite p,q and actual target hypotheses. Let 0<epsilon<norm(z0)<R. Assume the first residual component is strictly negative on both boundary circles and the ordinary real Frechet derivative at z0 is an invertible continuous real linear map L. Then the same actual nonzero nonphase competitor exists. Continuity of this explicit residual on the closed annulus, the original-root identity f(z0)=0, Hermitian preservation and actual root realization are proved, not assumed.

The reused CommonCore dictionary gives the entire raw observation, with actual append(append(left,block),right) and total length (p+2)+q. With prefix rows L_u=l A_u and right columns S_v=G(z)^2 A_v r, one has P=L dagger L, H=S S dagger, and Q2(w,wprime)=trace(P K_w H K_wprime dagger). This identity retains all sixteen complex entries and the affine scale. The prefix rank-at-most-two Schur record is not used.

At a common root the trial matrices are Hermitian and have determinant zero. The existing rank-one factor supplier factors each nonzero trial matrix. Hermitian symmetry makes its scalar multiple of an outer Gram real. Forward transfer and dual transfer preserve positive semidefiniteness. A nonpositive scalar would make the forward image nonpositive, contradicting a strictly positive diagonal entry of the positive definite target. Its positive square root supplies actual finite left and right boundaries. The inverse identities recover P,H exactly; no positive inverse is assumed.

For phase separation the fixed matrices I,C,B,BC span all complex two by two matrices. Positive target Grams supply explicit left and right inverses. A hypothetical phase equality therefore gives U M V=eta M for every matrix M. Nonzero eta makes U,V invertible; U commutes with every matrix and the existing scalar-center theorem gives U=h I, h nonzero. Thus the two actual prefix row families are proportional. Sampling words zero to the power p-1 followed by j gives the invertible column systems Ralpha and Rbeta, with determinants alpha delta and beta delta, forcing zeta=z0. The argument uses the actual arbitrary boundaries, not an old canonical chart.

The annular result directly consumes AnnularSecondZero.annular_second_zero. That supplier uses TauCeti.not_contractibleSpace_sphere, source revision 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported with its Apache-2.0 attribution and retained license at docs/reports/licenses/tauceti-sphere-port-LICENSE.txt. The imported C8 reconstruction remains attributed to Haobo Ma and Wenlin Zhang, Proof of Critch-Morton Conjecture 8, CC BY 4.0. Neither reused result is new root-realization mathematics.

This is a conditional root-to-actual result, not C9 or a genericity theorem, and earns zero solved-open-problem credit. General endpoint operator limits and determinant signs, universal all-length transversality, finite canonical-chart coverage and dominance, and genericity on the actual state and actual raw-density images remain separate obligations. No normalization, holomorphicity, strict derivative, regularity of other zeros, nonzero winding, clock, dynamics, positive physical inverse, stability or thermodynamic cost is asserted.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.B`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.C`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.G`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.K`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Regular`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.Sector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.alpha`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.annular_regular_root_actual_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.beta`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.core`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.delta`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalInverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.diagonalStarInverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.distinct_residual_root_actual_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseDualTransfer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.inverseTransfer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.iterate_smul`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.leftTarget`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.residual`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.rightTarget`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.transfer_smul`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialLeft`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization.trialRight`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore](OpenBoundaryMPSInteriorCommonCore.md)
- Dependency: [D5/S3/Topology/AnnularSecondZero](../../Topology/AnnularSecondZero.md)
