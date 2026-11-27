# Sharp probe count for the Jacobi endpoint Green column

## Abstract

Two full endpoint resolvent columns characterize agreement on the initial Jacobi component.

**Definition 1.1 (Initial Jacobi component).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.EndpointConnected`

*Formalization.* `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.EndpointConnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A site j belongs to the initial component when every lower bond strictly before j is nonzero. Site zero always belongs. If a bond vanishes, the component ends at the site before the first such bond.

**Theorem 1.2 (Adjacent Green minor).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.adjacent_green_minor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.adjacent_green_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complex tridiagonal matrix of positive size and assume every principal tail of each of the two shifts z₀I−H and z₁I−H is invertible. Write g(z) for the full first inverse column and mᵢ(z) for the first diagonal entry of the inverse of the tail starting at i. At consecutive sites p,i, the determinant gₚ(z₀)gᵢ(z₁)−gₚ(z₁)gᵢ(z₀) factors as gₚ(z₀)gₚ(z₁)bₚ(mᵢ(z₁)−mᵢ(z₀)), where bₚ is the lower bond at p. This follows by applying the Green-column transfer at each probe, including when bₚ vanishes.

**Theorem 1.3 (Exact detection by two opposite-half-plane probes).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.two_probe_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.two_probe_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H₀ and H₁ be Hermitian complex matrices of the same positive size, with H₀ and the difference V=H₁−H₀ tridiagonal. Fix z₀ with positive imaginary part and z₁ with negative imaginary part. The full first inverse columns of the shifted H₀ and H₁ coincide at both probes exactly when V has zero columns at every site of the initial component of H₀. Nonreal shifts and their Hermitian compressions are invertible. Their inverse diagonal imaginary parts have signs opposite to the probe's imaginary part, making the adjacent Green minor nonzero inside the component. The column equations reduce agreement to Vg(z)=0. Induction over the component eliminates earlier columns. In the first row past a zero bond only the last connected site can contribute, so the boundary entry also vanishes. Conversely, each reference Green column vanishes outside the initial component.

**Theorem 1.4 (Agreement at every nonreal probe).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.firstColumn_eq_of_two_probes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.firstColumn_eq_of_two_probes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the Hermiticity and tridiagonal support hypotheses, equality of the full first inverse columns at a probe with positive imaginary part and a probe with negative imaginary part implies equality at each nonreal spectral parameter. The two samples force V to vanish on the initial component, which supports the reference column at every such parameter.

**Definition 1.5 (Two-site reference).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSiteReference`

*Formalization.* `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSiteReference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference has zero diagonal and both off-diagonal entries equal to the real bond b.

**Definition 1.6 (Two-site perturbation).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSitePerturbation`

*Formalization.* `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSitePerturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real b and ε and complex z, the perturbation is ε times the outer product of x=(b,−conjugate(z)) with its conjugate transpose.

**Theorem 1.7 (A counterexample at any prescribed single probe).**

Lean statement: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.one_probe_two_site_adversary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.one_probe_two_site_adversary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a complex z with nonzero imaginary part, any nonzero real b and any positive real ε. For the two-site reference H₀ and the perturbation V above, H₀ and H₁=H₀+V are Hermitian. Both H₀ and V are tridiagonal, and both sites belong to the initial component of H₀. Their full first inverse columns agree at z even though V(0,0) is nonzero. The second row of the reference column equation gives orthogonality to x, so V annihilates the observed column.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.EndpointConnected`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.adjacent_green_minor`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.firstColumn_eq_of_two_probes`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.one_probe_two_site_adversary`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSitePerturbation`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.twoSiteReference`
- Truth anchor: `D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer.two_probe_eq_iff`
- Dependency: [D5/S3/Quantum/Matrix/JacobiEndpointResolvent](../JacobiEndpointResolvent.md)
