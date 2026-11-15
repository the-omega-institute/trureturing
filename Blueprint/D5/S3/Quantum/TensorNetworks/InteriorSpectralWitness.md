# Actual all-length spectral clearing witness

## Abstract

Actual all-length spectral clearing witness

**Definition 1.1 (The original canonical thirteen-coordinate witness).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.canonicalPoint`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.canonicalPoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The point is (0,0,1/2,0,1,0,0,0,0,0,1,1,1). Thus its core is the existing spectral witness, sigma=1 and eta=1+i.

**Theorem 1.2 (The complete raw-right scalar survives).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.native_b_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.native_b_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, let N=(p+2)+q. The actual b(p,q), evaluated at sector(witnessC,1), nativeLeft(witnessC,1), nativeRight(witnessC,1,N,(1,1+i)) and z(witnessC,1), is nonzero. The public fixed_witness_extraction identifies these data with the same accepted sector (2,0,1), left (1,1), z=1 and right (1/2)^N times (1,i). The exact sixteen-coordinate scale identity and b_right_scale multiply the existing b_nonzero evaluation by the nonzero real quartic ((1/2)^N)^4. No length-dependent scalar is dropped.

**Theorem 1.3 (The actual cleared numerator has a nonzero physical value).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.H_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.H_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, H(p,q) evaluated at the real spectral point (1,0) followed by canonicalPoint is nonzero. The exact physical clearing equality is used at the admissible fixed witness. A zero H would force the actual native b evaluation to vanish, contradicting native_b_witness. No complex-valued clearing theorem or fraction-field evaluation is assumed.

**Definition 1.4 (Unbarred free spectral coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeCore`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeCore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In COMPLEX13 ordered as c0,c1,c2,lambda,mu,barc0,barc1,barc2,barlambda,barmu,eta,bareta,sigma, c3=-c2 lambda mu and c4=c1+c2(lambda+mu).

**Definition 1.5 (Independent barred spectral coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeBarCore`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeBarCore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The barred copy uses independent polynomial variables, with barc3=-barc2 barlambda barmu and barc4=barc1+barc2(barlambda+barmu). No analytic conjugacy is imposed.

**Definition 1.6 (Literal FREE COMPLEX13 map on the existing REAL13 base).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.baseAssignment`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.baseAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Map each real part of cj to (cj+barcj)/2 and each imaginary part to -(i/2)(cj-barcj); sigma maps to the free sigma, and eta real and imaginary parts use the same split of eta,bareta. All halves are scalar coefficient polynomials.

**Definition 1.7 (Polynomial base map).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.phi`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The map is eval2Hom(C composed with Complex.ofRealHom,baseAssignment). Its injectivity is neither assumed nor required.

**Definition 1.8 (First free root).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.E`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

E=c2(lambda-mu).

**Definition 1.9 (Second independent free root).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.F`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

F=barc2(barlambda-barmu).

**Definition 1.10 (First literal free-variable swap).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapE`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The existing renameEquiv exchanges free lambda and mu, fixes every mapped canonical base coordinate, and maps E to -E while fixing F.

**Definition 1.11 (Second literal free-variable swap).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapF`

*Formalization.* `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The existing renameEquiv exchanges free barlambda and barmu, fixes every mapped canonical base coordinate, and maps F to -F while fixing E.

**Theorem 1.12 (Free-orbit nonvanishing of the actual lengthwise norm).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.normg_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.normg_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, normg of the actual four reduced g(p,q) and actual discriminant projections is a nonzero REAL13 polynomial. The witness evaluates the first free character to the nonzero physical H value: the cross is exactly one. The two polynomial automorphisms fix the mapped g coefficients and flip independent roots. Injectivity of these automorphisms and the polynomial-domain product prove all four character factors nonzero. The corrected character identity identifies their product with phi(normg); normg=0 would map to zero. No base-map injection, specialized-algebra domain, field degree, nonsquare premise, or norm-at-the-witness argument is used.

**Theorem 1.13 (Literal nonzero REAL13 certificate).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.P_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.P_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each p,q at least one, P(p,q) is nonzero. At canonicalPoint, Jden=1/64 and Wnorm=1; sigma is the nonzero coordinate polynomial. The norm factor is nonzero by the free-orbit proof, independently of its value at that witness. Multiply these nonzero polynomials in the real polynomial domain.

The physical witness proves the nonzero free character used in the orbit product. It does not assert that normg or P is nonzero at that specialization. The completed certificate and native positive-environment proofs are consumed by InteriorSpectralAmbiguity. Downstream InteriorSpectralAmbiguity.observed_interior_ambiguity supplies observed-Q3 descent: for every fixed N at least four, one common nonempty relatively open dense principal locus in the entire actual image supports ambiguity for every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This is a raw-state statement; it supplies no normalized-state or joint-marginal theorem. The N=3 boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full C9 remains open and solved-open-problem KPI is zero.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.E`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.F`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.H_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.P_nonzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.baseAssignment`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.canonicalPoint`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeBarCore`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.freeCore`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.native_b_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.normg_nonzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.phi`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapE`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness.swapF`
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate](InteriorSpectralCertificate.md)
