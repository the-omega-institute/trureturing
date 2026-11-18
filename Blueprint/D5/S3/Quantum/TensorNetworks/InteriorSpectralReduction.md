# InteriorSpectralReduction

## Abstract

Canonical spectral exclusion construction

**Definition 1.1 (Multiplication by the first real spectral coordinate).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MX`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MX` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The literal four by four matrix has columns encoding x times the basis (1,x,y,r), using x squared=(r+A)/2, xy=B/2 and rx=A x+B y. Halves are real constant polynomials.

**Definition 1.2 (Multiplication by the second real spectral coordinate).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MY`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MY` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The literal four by four matrix encodes y times the same basis using y squared=(r-A)/2, xy=B/2 and ry=B x-A y. No matrix-target commutative evaluation is defined.

**Definition 1.3 (Finite actual monomial sum).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For an ordinary polynomial G in two spectral variables over the actual REAL13 base, coefficient j is the sum over the finite support of G of coeff(G,m) times entry j of MX to the power m0 times MY to the power m1 applied to (1,0,0,0). The order is fixed and no matrix-commutation theorem is needed.

**Theorem 1.4 (Ordered monomial reduction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.monomial_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.monomial_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For any commutative ring T, ring map alpha from the actual REAL13 base, A,B and x,y,r satisfying the five displayed multiplication-table identities, the row (1,x,y,r) paired with the mapped ordered matrix monomial applied to (1,0,0,0) equals x to the power i times y to the power j for all natural i,j. The proof uses finite eigen-row identities and induction on powers.

**Theorem 1.5 (Four literal coefficients evaluate to the original polynomial).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every such target, map, parameters and five multiplication-table identities, and every G in the two spectral variables, eval2(alpha,(x,y),G)=alpha(g0)+alpha(g1)x+alpha(g2)y+alpha(g3)r, where each gj is the literal finite support sum. No domain or field premise is added.

This finite reduction is consumed by the nonzero lengthwise canonical exclusion certificate and its pointwise actual ambiguity theorem. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The existing Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MX`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.MY`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.coefficients_evaluation`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction.monomial_evaluation`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm](OpenBoundaryMPSInteriorSpectralNorm.md)
