# Actual interior polynomial transversality in eighteen real coordinates

## Abstract

Actual interior polynomial transversality in eighteen real coordinates

**Theorem 1.1 (Literal independent-trial real polynomials).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall s \in Sector,\; \forall l \in Function\left(Fin\left(2\right), Complex\right),\; \forall r \in Function\left(Fin\left(2\right), Complex\right),\; \forall zo \in Complex,\; (Regular\left(s\right)) \Rightarrow (\forall z \in Complex,\; (z \neq 0) \Rightarrow ((eval\left(slice\left(coordinates\left(s, l, r, zo\right), z\right), FL\left(p, q\right)\right) = cL\left(s, p, z\right) \cdot re\left(apply\left(residual\left(s, p, q, leftTarget\left(s, zo, l, p\right), rightTarget\left(s, zo, r, q\right)\right), z\right)\right)) \land (eval\left(slice\left(coordinates\left(s, l, r, zo\right), z\right), FR\left(p, q\right)\right) = cR\left(s, q, z\right) \cdot im\left(apply\left(residual\left(s, p, q, leftTarget\left(s, zo, l, p\right), rightTarget\left(s, zo, r, q\right)\right), z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.polynomial_clear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Construct the exact native core at the actual target z0 in paired complex polynomial variables. Forward left and right recurrences form the actual target matrices. The central G(z0) squared congruence is outside the right transfer iterate. The division-free adjugate and Schur recurrences then vary only the independent trial z. Cartesian conversion, real coefficient extraction and explicit reindexing give FL_pq and FR_pq over the real numbers in trial x,y plus sixteen actual coordinates. Their exact evaluations are cL times the real native residual and cR times its imaginary component.

**Theorem 1.2 (Differentiate trial variables before target substitution).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall s \in Sector,\; \forall l \in Function\left(Fin\left(2\right), Complex\right),\; \forall r \in Function\left(Fin\left(2\right), Complex\right),\; \forall zo \in Complex,\; ((Regular\left(s\right)) \land (zo \neq 0)) \Rightarrow (\forall D \in RealContinuousLinearEnd\left(Complex\right),\; (HasFDerivAt\left(residual\left(s, p, q, leftTarget\left(s, zo, l, p\right), rightTarget\left(s, zo, r, q\right)\right), D, zo\right)) \Rightarrow (eval\left(coordinates\left(s, l, r, zo\right), b\left(p, q\right)\right) = cL\left(s, p, zo\right) \cdot cR\left(s, q, zo\right) \cdot det\left(toLinearMap\left(D\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_eval_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The actual coordinate order is lambda.re,lambda.im,mu.re,mu.im,a.re,a.im,l0.re,l0.im,l1.re,l1.im,r0.re,r0.im,r1.re,r1.im,z0.re,z0.im. First form the formal trial determinant pderiv_x(FL) pderiv_y(FR)-pderiv_y(FL) pderiv_x(FR), then substitute x=z0.re,y=z0.im. This defines b_pq in sixteen real actual variables. At the native common root, for any ordinary real derivative D of the fixed-target residual, eval(b_pq)=cL(z0)cR(z0)det_R(D). The diagonal identity in changing target parameters is never differentiated.

**Theorem 1.3 (All positive exterior lengths have a nonzero polynomial).**

$$\forall p \in Nat,\; \forall q \in Nat,\; ((1 \le p) \land (1 \le q)) \Rightarrow ((eval\left(coordinates\left(fixedSector, leftBoundary, rightBoundary, 1\right), b\left(p, q\right)\right) \neq 0) \land (b\left(p, q\right) \neq 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, consume interior_q2_fixed_target_witness from the authoritative native transversality module, at sector (2,0,1), l=(1,1), r=(1,I), z0=1. Its real triangular derivative has nonzero determinant. The exact Jacobian identity and the strictly positive factors prove nonzero evaluation at this actual witness and hence b_pq is not the zero polynomial. There is no added witness, derivative invertibility or nonzero premise.

**Theorem 1.4 (Right-boundary amplitude restoration).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall theta \in Function\left(Fin\left(16\right), Real\right),\; \forall a \in Real,\; eval\left(scaleRight\left(a, theta\right), b\left(p, q\right)\right) = a^{4} \cdot eval\left(theta, b\left(p, q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_right_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every real a, replacing the actual right boundary r by a r multiplies its outer Gram and target quadratically. The full cleared right recurrence remains linear in this target, so its determinant row and the corresponding trial derivatives scale by a^4. The left row and both clearing factors are unchanged. Thus eval(b_pq) scales by exactly a^4, including a=0. This is the amplitude transport needed when a subsequent finite spectral descent extracts a dyadic boundary and restores a square-root amplitude. The derivative here has two real inputs and two real outputs. Spectral coefficient rank four is a separate algebraic notion.

**Theorem 1.5 (Actual annular ambiguity on the nonzero locus).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \forall s \in Sector,\; \forall l \in Function\left(Fin\left(2\right), Complex\right),\; \forall r \in Function\left(Fin\left(2\right), Complex\right),\; \forall zo \in Complex,\; (((((((1 \le p) \land (1 \le q)) \land (Regular\left(s\right))) \land (zo \neq 0)) \land (PosDef\left(leftTarget\left(s, zo, l, p\right)\right))) \land (PosDef\left(rightTarget\left(s, zo, r, q\right)\right))) \land (eval\left(coordinates\left(s, l, r, zo\right), b\left(p, q\right)\right) \neq 0)) \Rightarrow (\exists phi \in Function\left(Word\left(p + 2 + q\right), Complex\right),\; (((Member\left(phi, openBoundaryMPS\left(p + 2 + q\right)\right)) \land (phi \neq 0)) \land (rawInterior\left(p, 2, q, phi\right) = rawInterior\left(p, 2, q, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right))) \land (\neg (\exists eta \in Complex,\; (norm\left(eta\right) = 1) \land (phi = smul\left(eta, mpsState\left(p + 2 + q, core\left(s, zo, 0\right), core\left(s, zo, 1\right), l, r\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.nonzero_locus_actual_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

On a regular sector with nonzero actual z0 and positive definite actual left and right environments, nonzero evaluation of b yields an invertible ordinary real derivative. Differentiability follows from the literal polynomial slices divided by the nonzero clearing factors on a neighborhood of z0. The endpoint-sign supplier produces radii enclosing z0 with a negative first residual component on both entire circles. The native annular root-realization theorem then constructs a nonzero actual finite MPS with identical entire rawInterior p 2 q and no unit-phase relation to the target. Positive actual environments remain hypotheses.

These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_eval_derivative`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_nonzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.b_right_scale`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.nonzero_locus_actual_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial.polynomial_clear`
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance](InteriorPolynomialClearance.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus](InteriorPolynomialRealCalculus.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns](OpenBoundaryMPSInteriorEndpointSigns.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality](OpenBoundaryMPSInteriorTransversality.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient](OpenBoundaryMPSQuotient.md)
