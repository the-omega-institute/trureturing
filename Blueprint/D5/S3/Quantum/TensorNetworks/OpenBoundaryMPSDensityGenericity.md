# Generic recovery in the actual open-boundary MPS image

## Abstract

An intrinsic dense real-algebraic locus for raw prefix recovery

**Definition 1.1 (Real coordinates of complex amplitudes).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.realCoordinates`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.realCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The two copies of the index set contain the real and imaginary parts, with values in the real numbers. This coordinate map is distinct from PhasePolynomial.cartesian, whose values and polynomial coefficient field remain complex.

**Theorem 1.2 (Continuity of full real and imaginary amplitude coordinates).**

$$\forall (iota: Type), (\operatorname{Continuous}\left(\operatorname{realCoordinates}\left(iota\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.continuous_realCoordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The coordinate map from iota-indexed complex amplitudes to the two real coordinate copies is continuous for every index type. Continuity is proved coordinatewise and applies in particular to physical-mass-one normalization.

**Definition 1.3 (The four-entry transfer matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.transferMatrix`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.transferMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Rows and columns are indexed by pairs of bond indices. The (i,j),(k,l) entry is the sum over the two physical symbols of A_s(i,k) times the conjugate of A_s(j,l). Matrix multiplication on the flattened four complex entries is exactly the original transfer operator. Its determinant is nonzero precisely when that complex linear transfer is injective.

**Definition 1.4 (Polynomial transfer numerators).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.numeratorTransfer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.numeratorTransfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Reuse matrixNumerator from the original Cramer reconstruction. Its first entry factor uses the t variables; the second uses independent conjugate-t variables and coefficient conjugation. The determinant is therefore a polynomial before imposing actual conjugacy. No second Cramer construction or rational parameter map is introduced.

**Definition 1.5 (One polynomial with real coefficients).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.recoveryPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.recoveryPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Multiply the original chartPoly by the numerator-transfer determinant in independent t and conjugate-t variables. Apply the existing PhasePolynomial.toCartesian. Split the resulting coefficients into their real and imaginary parts and add the squares of the two real polynomials. Evaluation is exactly the complex norm square of the original product. Complex real and imaginary parts are used as additive coefficient maps, never as ring homomorphisms.

**Theorem 1.6 (Exact polynomial characterization of the reconstruction conditions).**

$$\forall (t: \operatorname{Word}\left(3\right) \to \mathbb{C}), ((\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(t\right), \operatorname{recoveryPolynomial}\left(\right)\right) \ne 0) \Leftrightarrow ((\operatorname{MvPolynomial.eval}\left(t, \operatorname{OpenBoundaryMPSMarginalBirationality.chartPoly}\left(\right)\right) \ne 0) \land (\operatorname{Function.Injective}\left(\operatorname{OpenBoundaryMPSDensityRecovery.transfer}\left(\operatorname{OpenBoundaryMPSDensityRecovery.canonicalCore}\left(t\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

On the coherent chart, the original chart_scalars formula identifies each reconstructed matrix with c times its matrixNumerator evaluation, where c is nonzero. Consequently the transfer matrix is multiplied by c times its conjugate, and the four-dimensional determinant by its fourth power. The exact norm-square evaluation proves the displayed equivalence. This fixed-selector condition is sufficient for ObservableChart; no equivalence with its existential selector is asserted.

**Definition 1.7 (The fixed observed column).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.fixedTensor`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.fixedTensor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For the all-zero three-bit word e, retain Q at column e. Equivalently this is Q times the standard basis vector at e. The selector is fixed and depends on no unknown MPS parameters.

**Definition 1.8 (A principal condition in observed density coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.observedPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.observedPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Rename the variables of recoveryPolynomial into the real and imaginary coordinates of the e column of the full observed Q3 matrix. Thus this is a literal real multivariate polynomial in observed entries, supported on sixteen real coordinates. It is not an analyticity-only or parameter-open condition.

**Definition 1.9 (The quadratic raw-density substitution).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.statePolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.statePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Substitute the real and imaginary parts of Q3(psi) at its fixed column into recoveryPolynomial. The real coordinate is the complement sum of real-real plus imaginary-imaginary products; the imaginary coordinate is imaginary-real minus real-imaginary. This polynomial evaluates exactly to observedPolynomial on the actual raw Hermitian prefix density of every complex amplitude function, without an MPS hypothesis.

**Definition 1.10 (Pullback through the original MPS parametrization).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.parameterPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.parameterPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Substitute the Cartesian real and imaginary parts of the existing parameterPolys into statePolynomial. The result has real coefficients on the original twelve complex, hence twenty-four real, matrix-and-boundary coordinates. The proof uses the supplier parameter_eval and parameter_image with their original telescopes.

**Definition 1.11 (The intrinsic relative principal open set).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.goodStates`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.goodStates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The source is the subtype of the literal parametrized image openBoundaryMPS(3+m), not its Zariski closure. A state belongs exactly when observedPolynomial evaluated on the real and imaginary entries of its raw first-three-site density is nonzero. The statePolynomial pullback proves relative Euclidean openness; the displayed observed polynomial supplies the real-algebraic presentation.

**Theorem 1.12 (Nonempty dense actual-image generic recovery at every length).**

$$\forall (m: \mathbb{N}), ((((\operatorname{Nonempty}\left(\operatorname{goodStates}\left(m\right)\right)) \land (\operatorname{IsOpen}\left(\operatorname{goodStates}\left(m\right)\right))) \land (\operatorname{Dense}\left(\operatorname{goodStates}\left(m\right)\right))) \land (\forall (psi: \operatorname{Subtype}\left(\operatorname{OpenBoundaryMPSMarginalBirationality.openBoundaryMPS}\left(3 + m\right)\right)), ((psi \in \operatorname{goodStates}\left(m\right)) \to (\forall (phi: \operatorname{Word}\left(3 + m\right) \to \mathbb{C}), ((phi \in \operatorname{OpenBoundaryMPSMarginalBirationality.openBoundaryMPS}\left(3 + m\right)) \to ((\operatorname{OpenBoundaryMPSDensityRecovery.rawPrefix}\left(3, m, phi\right) = \operatorname{OpenBoundaryMPSDensityRecovery.rawPrefix}\left(3, m, \operatorname{Subtype.val}\left(psi\right)\right)) \Leftrightarrow (\exists (z: \mathbb{C}), ((\operatorname{norm}\left(z\right) = 1) \land (phi = \operatorname{smul}\left(z, \operatorname{Subtype.val}\left(psi\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.intrinsic_recovery_genericity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural complement length m, goodStates m is nonempty, open and dense in the subtype topology of the actual free-boundary state image. In particular this covers every original length N=3+m at least four. Every target in this locus is recovered up to a unit complex phase against every actual competitor. The competitor carries no genericity, coherent-chart or regular-parameter premise. The observation is the source's raw prefix Q3, with affine scale retained.

The uniform actual witness uses the original A0=[[1,2],[3,4]], A1=[[5,6],[7,8]], l=(1,0), r=(1,2). Its fixed observed coherent vector has effective boundary E^m(rr-dagger) times (37,54). The real symmetric tail entries a,b,c stay strictly positive under the exact recurrence (26a+64b+40c,38a+92b+56c,58a+136b+80c). The effective boundary is (37a+54b,37b+54c). The original positive-boundary chart theorem applies directly. Exact linear combinations of the four output entries certify injectivity of the original transfer. The reused three-site gauge preserves transfer injectivity by invertible conjugate sandwiches and a nonzero scalar. This density-column witness is distinct from the coherent sum-tail used in the minimality supplier.

The real polynomial parameter pullback is nonzero at this actual witness. Multidimensional real analytic uniqueness makes its zero locus have empty interior in the full connected real parameter space. Continuity of the original polynomial MPS map sends every parameter value into the closure of the image of good parameters. The exact pullback identities put that image inside goodStates. This proves density in the actual state image without assuming the MPS map is open, or identifying its Euclidean image with a complex Zariski closure.

The existing observable_chart_phase_recovery supplies the final arbitrary-competitor unit-phase equivalence. The gauge and coherent reconstruction are due to the original Conjecture 8 supplier, including the Ma-Zhang canonical inverse. This is the recovery-genericity portion of the prefix reading of Conjecture 9. Generic-point two-site minimality in the full actual state image is not established by this recovery theorem; the separate canonical-parameter open collision theorem does not supply that descent. No Conjecture 9 resolution, all-interior-window theorem, normalized-state theorem, physical inverse, stability, dynamics or thermodynamic assertion is made.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.continuous_realCoordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.fixedTensor`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.goodStates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.intrinsic_recovery_genericity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.numeratorTransfer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.observedPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.parameterPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.realCoordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.recoveryPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.recoveryPolynomial_ne_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.statePolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity.transferMatrix`
- Dependency: [D5/S3/Quantum/Algebra/CommonPhasePolynomial](../Algebra/CommonPhasePolynomial.md)
- Dependency: [D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients](../Algebra/Polynomials/ComplexPolynomialCoefficients.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery](OpenBoundaryMPSDensityRecovery.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality](OpenBoundaryMPSTwoSiteMinimality.md)
