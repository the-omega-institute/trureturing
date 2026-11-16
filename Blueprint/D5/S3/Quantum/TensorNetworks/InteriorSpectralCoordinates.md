# InteriorSpectralCoordinates

## Abstract

Canonical spectral exclusion construction

**Definition 1.1 (Spectral and canonical indexing).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.point`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.point` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The ordinary Fin15 real assignment has spectral Re(e), Im(e) at indices zero and one, followed by the existing Fin13 canonical coordinates in their unchanged order.

**Definition 1.2 (Independent polynomial fractions).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.Frac`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.Frac` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

A fraction stores two ordinary complex polynomials. Addition, multiplication, inversion and natural powers construct literal numerator and denominator polynomials. Inversion is used only when the interpreted value is nonzero. The real projections use nr dr+ni di and ni dr-nr di over dr squared+di squared, with no polynomial division.

**Definition 1.3 (The actual eight complex native entries).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.nativeTerms`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.nativeTerms` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each natural length N the eight expressions are lambda, mu, a, l0, l1, r0, r1, z, with the actual spectral frame, its actual matrix inverse, the diagonal rho gauge, and r=u to the power N times S inverse applied to (1,eta). No native right entry is required nonzero. N=0 remains included.

**Definition 1.4 (Literal REAL15 numerators).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.numerator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The sixteen entries alternate the real and imaginary numerators of the eight actual complex entries.

**Definition 1.5 (Literal REAL15 denominators).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.denominator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Each coordinate keeps its independently constructed denominator norm square; no common power or degree bound is imposed.

**Theorem 1.6 (Exact physical ratios and every inverse guard).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.native_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.native_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every real canonical assignment x, complex e satisfying Admissible(coreCoordinates(x),e), and every natural N, every one of the sixteen real denominator evaluations is nonzero. The vector of numerator evaluations divided by denominator evaluations equals exactly InteriorPolynomial.coordinates of the existing extracted sector, nativeLeft, nativeRight at full length N and raw original right column (1,eta(x)), and z. The proof uses spectral_frame for the frame determinant and all nonzero conjugated entries, native_extraction for detS and the native left row, explicit two by two adjugates, and real complex-division formulas. The same assertion applies separately to e and -e, since only Admissible is used.

These concrete coordinates are consumed by the nonzero lengthwise canonical exclusion certificate and its pointwise actual ambiguity theorem. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The existing Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.Frac`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.denominator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.nativeTerms`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.native_coordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.numerator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates.point`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial](OpenBoundaryMPSInteriorPolynomial.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQ2PolynomialFiber](OpenBoundaryMPSQ2PolynomialFiber.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction](OpenBoundaryMPSSpectralExtraction.md)
