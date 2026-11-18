# Ordinary real calculus for independent trial polynomials

## Abstract

Ordinary real calculus for independent trial polynomials

**Theorem 1.1 (Ordinary real polynomial slice derivative).**

$$\forall K \in Type,\; \forall F \in RealTrialPolynomial\left(K\right),\; \forall theta \in Function\left(K, Real\right),\; \forall z \in Complex,\; HasFDerivAt\left((\lambda (w: Complex) \mapsto (eval\left(slice\left(theta, w\right), F\right))), sliceDerivative\left(F, theta, z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.hasFDerivAt_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For an arbitrary real polynomial F in two independent trial coordinates and any target coordinate type, hold every target coordinate constant. Formal pderiv in trial x and y gives the ordinary real Frechet derivative: eval(pderiv_x F) times reCLM plus eval(pderiv_y F) times imCLM. Polynomial induction proves the constant, sum and multiplication cases using the existing pderiv rules and real calculus.

**Theorem 1.2 (The real two by two determinant).**

$$\forall D \in RealContinuousLinearEnd\left(Complex\right),\; det\left(toLinearMap\left(D\right)\right) = re\left(D\left(1\right)\right) \cdot im\left(D\left(I\right)\right) - re\left(D\left(I\right)\right) \cdot im\left(D\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.real_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The columns of the ordinary real derivative are its values on 1 and I; the rows are real and imaginary outputs. The basisOneI change-of-basis theorem identifies this two by two determinant with LinearMap.det over the real field.

**Theorem 1.3 (Clearing scales the two derivative rows).**

$$\forall K \in Type,\; \forall F \in RealTrialPolynomial\left(K\right),\; \forall H \in RealTrialPolynomial\left(K\right),\; \forall theta \in Function\left(K, Real\right),\; \forall z \in Complex,\; \forall f \in Function\left(Complex, Complex\right),\; \forall D \in RealContinuousLinearEnd\left(Complex\right),\; \forall c \in Function\left(Complex, Real\right),\; \forall e \in Function\left(Complex, Real\right),\; ((((((f\left(z\right) = 0) \land (HasFDerivAt\left(f, D, z\right))) \land (DifferentiableAt\left(Real, c, z\right))) \land (DifferentiableAt\left(Real, e, z\right))) \land (EventuallyEq\left(nhds\left(z\right), (\lambda (w: Complex) \mapsto (eval\left(slice\left(theta, w\right), F\right))), (\lambda (w: Complex) \mapsto (c\left(w\right) \cdot re\left(f\left(w\right)\right)))\right))) \land (EventuallyEq\left(nhds\left(z\right), (\lambda (w: Complex) \mapsto (eval\left(slice\left(theta, w\right), H\right))), (\lambda (w: Complex) \mapsto (e\left(w\right) \cdot im\left(f\left(w\right)\right)))\right))) \Rightarrow (eval\left(slice\left(theta, z\right), trialJacobian\left(F, H\right)\right) = c\left(z\right) \cdot e\left(z\right) \cdot det\left(toLinearMap\left(D\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.cleared_jacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let the polynomial rows agree locally with c times Re(f) and e times Im(f). At a common root of f, differentiable clearing factors contribute no derivative-of-factor term. Uniqueness of the ordinary real derivative identifies the formal trial Jacobian with c(z) e(z) det_R(D). All target coordinates remain fixed. No holomorphic derivative is used.

These are parameter-locus statements for finite native unnormalized MPS observations. Canonical chart dominance, genericity on actual full-state or actual raw-density images, and the full Critch-Morton C9 problem remain separate obligations. No solved-open-problem credit, clock, dynamics, energy, positive physical inverse or thermodynamic cost follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.cleared_jacobian`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.hasFDerivAt_slice`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorPolynomialRealCalculus.real_det`
