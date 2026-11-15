# InteriorSpectralCertificate

## Abstract

Canonical spectral exclusion construction

**Definition 1.1 (Actual cleared Jacobian numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.H`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each fixed p,q, H is chosen by the existing Q2PolynomialFiber.clear_polynomial applied to the actual native b(p,q) and the concrete sixteen numerator and denominator polynomials at N=(p+2)+q. Its equality is used only at real physical points.

**Definition 1.2 (Actual clearing denominator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.Bclear`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.Bclear` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The same existing real clearing theorem supplies B, whose evaluation is nonzero at every real point where all sixteen concrete denominators are nonzero.

**Theorem 1.3 (Exact actual b equality on admissible physical points).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.clearing_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.clearing_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For all p,q, every real canonical x and every admissible complex root e, B evaluated at the REAL15 physical point is nonzero and the actual native b evaluation equals H/B there. The native sector, both complete boundaries, z and full state length are those of SpectralExtraction. The proof consumes native_coordinates and the original independent-denominator clear_polynomial, without a field-valued rationality adapter.

**Definition 1.4 (Division-free cross numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Ccross=4 c2 bar(c2)+(bar(h)+f)(h-e), where h=c4-c1, e=X+iY and f=X-iY. Conjugation is coefficientwise and all REAL15 variables are real.

**Definition 1.5 (Literal real cross exclusion).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The polynomial is realCoeff(Ccross) squared+imagCoeff(Ccross) squared.

**Definition 1.6 (Actual spectral polynomial to reduce).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g15`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g15` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The consumed REAL15 input is H(p,q) times crossNorm, with H coming from the actual b clearing.

**Definition 1.7 (Explicit Fin15 split).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.gIter`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.gIter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Use finSumFinEquiv for Fin2 plus Fin13, followed by the existing sumRingEquiv, so that the first two spectral variables become polynomial variables and the canonical thirteen become coefficients.

**Definition 1.8 (Real discriminant coefficient polynomial).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrR`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The real coefficient projection of the actual canonical discriminant D.

**Definition 1.9 (Imaginary discriminant coefficient polynomial).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrI`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrI` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The imaginary coefficient projection of the same canonical discriminant D.

**Definition 1.10 (Actual four reduced REAL13 coefficients).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Apply the finite MX/MY support sum to gIter(p,q) with the actual discriminant real and imaginary coefficient polynomials.

**Definition 1.11 (Literal length-dependent REAL13 certificate).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.P`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each fixed p,q define P=X10 Jden Wnorm normg(g(p,q),ReCoeff(D),ImCoeff(D)). InteriorSpectralWitness proves P nonzero for positive p,q by the free orbit. certificate_native proves the physical branch conditions; InteriorSpectralEnvironments supplies both true positive targets, consumed by InteriorSpectralAmbiguity. This does not assert one polynomial for all lengths.

**Theorem 1.12 (Exact physical Schur cross adapter).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every canonical real x and complex e with c2 nonzero, Ccross at the real physical point equals (4 normSq(c2))(1+conjugate(lambda)mu), using the actual SpectralExtraction.lambda and mu. No regularity hypothesis is assumed; the equality proves the precise nonzero multiplier relation needed later.

**Theorem 1.13 (Exact physical squared modulus).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every real Fin15 assignment a, crossNorm evaluates to the actual complex norm square of Ccross evaluated at the complex cast of a.

**Theorem 1.14 (Actual REAL15 evaluation of the finite reduction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For all p,q, real canonical x and complex e with e squared=D(coreCoordinates x), the evaluation of H times crossNorm at the physical REAL15 point equals g0(x)+g1(x) Re(e)+g2(x) Im(e)+g3(x) normSq(e). The proof verifies the Fin2 plus Fin13 permutation and sumRingEquiv on polynomial generators, derives all five MX/MY table relations from the complex square equation, and consumes the literal finite support identity. No admissibility premise or rational-function evaluation is used in this reduction.

**Theorem 1.15 (Both physical branches and exact raw scalar).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.certificate_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.certificate_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For all p,q, every real canonical x with positive sigma and P(p,q)(x) nonzero, and EVERY complex e with e squared=D(coreCoordinates x), extraction is Admissible, its actual sector is Regular, and actual native b(p,q) is nonzero at the native left column, full nativeRight at N=(p+2)+q of sqrt(sigma) times (1,eta), and actual native z. Since e is universal, both e and -e are included. The character product excludes a zero physical H crossNorm. Jden supplies all native inverse guards; cross_native supplies the Schur cross. Exact real clearing supplies b at (1,eta), and the original quartic b_right_scale restores sqrt(sigma). No condition on the first native right entry is assumed.

**Theorem 1.16 (Conditional actual canonical/native endpoint with full raw scale).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.canonical_actual_ambiguity_of_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.canonical_actual_ambiguity_of_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each p,q at least one, every real canonical x, admissible complex e, arbitrary original complex right column R, Regular extracted sector, BOTH actual native leftTarget and rightTarget PosDef premises, and nonzero actual native b evaluation, there exists a nonzero actual length-(p+2+q) MPS with the same entire raw two-site interior as the original canonical state and with no unit-phase relation to that canonical state. The conclusion retains every conjunct from nonzero_locus_actual_ambiguity. The proof applies that actual theorem and the public raw_amplitude equality with nativeRight=u^N S inverse R. The rightTarget premise includes the outer G squared congruence. This theorem is an explicitly conditional intermediate consumed by canonical_exclusion_actual_ambiguity, which discharges these hypotheses on the certificate locus.

This unit proves lengthwise canonical parameter exclusion and pointwise actual ambiguity. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.Bclear`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.H`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.P`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.canonical_actual_ambiguity_of_native`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.certificate_native`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.clearing_native`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.crossNorm_eval`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.cross_native`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrI`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.discrR`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g15`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.gIter`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate.g_evaluation`
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates](InteriorSpectralCoordinates.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralReduction](InteriorSpectralReduction.md)
