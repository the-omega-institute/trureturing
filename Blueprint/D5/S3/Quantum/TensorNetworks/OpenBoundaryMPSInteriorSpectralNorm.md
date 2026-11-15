# OpenBoundaryMPSInteriorSpectralNorm

## Abstract

Canonical spectral exclusion construction

**Definition 1.1 (Original spectral exclusion numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalHbase`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalHbase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In the original five-complex canonical coordinate polynomials, form c2 D U (U+D), using h=c4-c1, D=h squared+4 c2 c3, t0=c1-c0 c2, t1=1+c3-c0 c4 and U=h t0 t1-c2 t1 squared+c3 t0 squared.

**Definition 1.2 (Real denominator exclusion factor).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalJden`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalJden` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The factor is the sum of the squares of the coefficientwise real and imaginary parts of the canonical spectral exclusion numerator.

**Definition 1.3 (Canonical right-seed determinant).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalW`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

W=c2 eta squared+(c1-c4)eta-c3 in the existing complex polynomial ring with thirteen real-coordinate variables.

**Definition 1.4 (Real right-boundary factor).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalWnorm`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalWnorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The sum of the squares of coefficientwise real and imaginary parts of W is an ordinary real polynomial.

**Definition 1.5 (Literal even-pair coefficient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.K0`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.K0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For four actual real base polynomials g0,g1,g2,g3 and real base polynomials A,B, K0=g0 squared+(A squared+B squared)g3 squared-(1/2)A(g1 squared-g2 squared)-B g1 g2. Every half is a constant polynomial C(1/2).

**Definition 1.6 (Literal mixed-pair coefficient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.H0`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.H0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

H0=2 g0 g3-(1/2)(g1 squared+g2 squared), with scalar half represented by a constant polynomial.

**Definition 1.7 (Literal REAL13 four-character norm).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.normg`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.normg` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The ordinary real polynomial is K0 squared-(A squared+B squared)H0 squared. No specialized coefficient algebra is assumed to be a domain.

**Definition 1.8 (Lengthwise certificate assembly).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.spectralCertificate`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.spectralCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Given the four reduced coefficients and A,B, the expression is X10 times canonicalJden times canonicalWnorm times normg. Its concrete nonvanishing and native consumer are proved by InteriorSpectralWitness and InteriorSpectralAmbiguity.

**Definition 1.9 (Independent complex characters).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In any commutative complex algebra, h(E,F)=g0+(1/2)g1(E+F)-(i/2)g2(E-F)+g3 EF. The independent square relations are E squared=a+i b and F squared=a-i b.

**Definition 1.10 (Character even coefficient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairK`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The generic character expression corresponding to K0 is built in the target commutative complex algebra with the same scalar halves.

**Definition 1.11 (Character EF coefficient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairH`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The generic character expression corresponding to H0 uses the same four coefficients and scalar half.

**Theorem 1.12 (Correct simultaneous sign pairing).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_opposite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every commutative complex algebra, all four coefficients and a,b,E,F satisfying the two square relations, h(E,F)h(-E,-F)=pairK+pairH EF. The pair flips both signs together. No nonzero, nonsquare or field-degree premise is used.

**Theorem 1.13 (Correct mixed opposite pairing).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Under the same complete hypotheses, h(-E,F)h(E,-F)=pairK-pairH EF. This follows from the simultaneous opposite pair applied at -E,F.

**Theorem 1.14 (Consumed four-character product).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_four_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_four_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Under the same complete hypotheses, h(E,F)h(-E,F)h(E,-F)h(-E,-F)=pairK squared-(a squared+b squared)pairH squared. The proof consumes the two corrected opposite pair identities and E squared F squared=a squared+b squared. A single nonzero specialization of one character does not prove this norm nonzero.

This unit proves lengthwise canonical parameter exclusion and pointwise actual ambiguity. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI remains zero. The Ma-Zhang C8 canonical supplier and its CC BY 4.0 attribution are retained. No dynamics, physical inverse, energy or thermodynamic assertion follows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.H0`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.K0`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalHbase`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalJden`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalW`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.canonicalWnorm`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_four_factor`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_mixed`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.character_opposite`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.normg`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairH`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.pairK`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm.spectralCertificate`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial](OpenBoundaryMPSInteriorPolynomial.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQ2PolynomialFiber](OpenBoundaryMPSQ2PolynomialFiber.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction](OpenBoundaryMPSSpectralExtraction.md)
