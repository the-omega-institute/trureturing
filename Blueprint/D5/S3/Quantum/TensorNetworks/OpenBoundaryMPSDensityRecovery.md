# Open-boundary recovery from a Hermitian prefix density

## Abstract

A raw first-three-site reduced density identifies every actual free-boundary binary bond-two competitor up to phase, conditional on a shared observable coherent chart and injective reconstructed transfer.

**Definition 1.1 (Actual amplitude columns).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.amplitudeColumns`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.amplitudeColumns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For a state ψ of length k+m, the row u and column b contain ψ at the concatenated word ub. These are coordinates of the original state, with no summation or normalization.

**Definition 1.2 (The raw Hermitian partial trace).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.rawPrefix`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.rawPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Multiply the amplitude-column matrix C by its conjugate transpose. The entry (u,v) is the sum over all complement words b of ψ(ub) times the complex conjugate of ψ(vb). This is Q_k in the displayed prefix map following Critch–Morton Conjecture 9. It preserves the norm-squared scale on the unnormalized cone; it is distinct from the coherent improperMarginal in Conjecture 8.

**Definition 1.3 (The virtual prefix map).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.prefixMap`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.prefixMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The row w is l times the ordered matrix word A_w. It maps a two-dimensional right virtual vector to its prefix amplitudes, using the existing PeriodicMPSParentIntersection.wordMatrix and the bilinear complex dot product of mpsState.

**Definition 1.4 (Actual complement columns).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.tailMap`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.tailMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The column b is A_b r, with the same symbol matrices and the actual independent free right boundary r. Thus the amplitude columns factor exactly as prefixMap times tailMap.

**Definition 1.5 (Linear transfer without a normalization assumption).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.transfer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The map sends X to A₀ X A₀† + A₁ X A₁† on complex two by two matrices. Its m-fold iterate on rr† is the Gram matrix of the length-m complement columns. No trace-preservation, unitality or positivity of an inverse is assumed.

**Definition 1.6 (Reuse of the coherent reconstruction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.canonicalCore`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.canonicalCore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

This is exactly OpenBoundaryMPSMarginalBirationality.reconstructedMatrix evaluated at the same three-site coherent tensor t. The supplier's chartPoly, reconstructedLeft and triple_gauge are reused with their original definitions and proof. No second support-rigidity or core-reconstruction theorem is introduced.

**Definition 1.7 (An intrinsic condition on the observed density).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.ObservableChart`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.ObservableChart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

There exists a complex vector v on three-bit words such that t = rawPrefix 3 m ψ times v has chartPoly(t) nonzero and transfer(canonicalCore t) is injective on all complex two by two matrices. Both tests depend only on the observed Q₃. The chart retains every factor of the supplier polynomial, including the reconstructed sum determinant. This definition asserts neither nonemptiness nor density.

**Theorem 1.8 (Phase recovery against every actual competitor).**

$$\forall (m: \mathbb{N}), (\forall (\psi: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3 + m\right) \to \mathbb{C}), (\forall (\phi: \operatorname{D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection.Word}\left(3 + m\right) \to \mathbb{C}), ((\psi \in \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS}\left(3 + m\right)) \to ((\phi \in \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS}\left(3 + m\right)) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.ObservableChart}\left(m, \psi\right)) \to ((\operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix}\left(3, m, \phi\right) = \operatorname{D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix}\left(3, m, \psi\right)) \Leftrightarrow (\exists (z: \mathbb{C}), ((\operatorname{norm}\left(z\right) = 1) \land (\phi = \operatorname{HSMul.hSMul}\left(z, \psi\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.observable_chart_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The target ψ and competitor φ belong to the literal parametrized image openBoundaryMPS(3+m), with arbitrary complex two by two matrices and independent free complex boundary vectors. Only ψ is required to satisfy ObservableChart. The result covers every natural m; the intended Conjecture 9 lengths have m at least one. Equality of Q₃ is equivalent to φ=zψ for a complex scalar of norm one.

Choose t=Q₃v. For every actual realization of either state, factor its amplitude-column matrix as F₃T. Matrix multiplication gives t=F₃γ for an induced virtual vector γ. Hence the same t is an actual coherent three-site MPS for both realizations, even when the competitor parameters are singular. Apply the existing triple_gauge directly to each realization; it supplies the same reconstructed left boundary and symbol matrices. At length n the free right boundary becomes q=(s times s to the power minus n)Ur, and the physical amplitude function is unchanged.

The chart's slice determinant factors through the rows lA_i, A₀ and the columns A_iγ. Its nonvanishing makes the rows lA_i and A₀ invertible. Restricting F₃ to the rows indexed by (i,0,0) therefore proves injectivity of F₃. This is a rank consequence of the supplied chart, not another gauge theorem.

For the common canonical core, Q₃=F₃ E^m(qq†) F₃†. Injectivity of F₃ cancels the two sandwiches; injectivity of E cancels its iterate. Equality of the two rank-one boundary Grams gives q′=zq with norm(z)=1, including the zero-boundary case. Linearity then propagates the same phase to the whole state. Conversely a unit phase cancels against its conjugate in every raw density entry.

This is a conditional reconstruction bridge toward Critch–Morton Conjecture 9, not an OpenProblemResolutionClaim. An intrinsic nonempty dense relative real-algebraic open locus for every length at least four, and the no-fewer clause asserting generic two-site nonidentifiability, remain obligations of the original problem. No all-interior-window interpretation is asserted.

The gauge reconstruction is supplied by the existing Conjecture 8 formalization. The present mathematical addition is the Hermitian density bridge with a common observed coherent vector and arbitrary actual competitors. Injectivity here concerns a finite-dimensional linear map. Its algebraic inverse is not asserted to be completely positive or implementable. The theorem provides no stability, sample complexity, dynamics, time group, Hamiltonian, clock, energy or thermodynamic cost.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.ObservableChart`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.amplitudeColumns`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.canonicalCore`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.observable_chart_phase_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.prefixMap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.rawPrefix`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.tailMap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery.transfer`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality](OpenBoundaryMPSMarginalBirationality.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection](PeriodicMPSParentIntersection.md)
