# The balanced one-photon minimum and coherent attainment

## Abstract

Every coherent density attains the balanced one-photon spectral minimum over all densities.

The balanced one-photon all-density spectral minimum and attainment by every coherent input are already proved in `D5/L/Entropy/he2026energy`, Theorem 2 (PDF page 5) and Appendix A.2-A.3 (PDF pages 18-19). This attributed formalization preserves that physical result. No new literature resolution or priority for the odd-occupation application is claimed.

The channel is the original attenuator (1/2) balanced (pointMassEnvironment 1), on the complete Attenuator.DensityOperator domain. Its native extended spectral entropy has attained minimum ENNReal.ofReal(Real.log 2), and every coherentDensity alpha attains it for every complex alpha. The comparison input rho is an arbitrary actual density, with no support, rank, energy or entropy restriction.

This is the balanced pure-one-photon case relevant to Conjecture 1 in `D5/L/QuantumStates/vanherstraeten2024nongaussian`, Section IV.B (PDF page 11). The paper already gives the vacuum output spectrum (1/2,1/2) and describes additional candidate minimizers in this case. These native proofs acknowledge both the original problem source and the prior written result. No uniqueness of coherent minimizers, odd-n>1 attainment, full all-occupation/all-transmissivity resolution, or equivalence to the separate basis-infimum entropy API is claimed.

**Theorem 1.1 (The density and pure-input channels agree).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.attenuator_pureDensity_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.attenuator_pureDensity_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every n : Nat and every completed Fock x with norm(x)=1, attenuatorOperator (1/2) balanced (pointMassEnvironment n) (pureDensity x hx) = pureAttenuatorOperator (1/2) balanced (pointMassEnvironment n) x. This bridge is at balance and follows from the original definitions. The positive square root of the rank-one projector is that projector. Its occupation columns yield coefficients inner(x,e_m) with squared norms summing to one. Proved norm-summability of the product series reduces the original rank-one density mixture to the actual pure partial trace. Both exact-attainment proofs consume this bridge.

**Theorem 1.2 (Vacuum attains log two).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_entropy` (`✓ std3`). ∎

*Citation.* Zixuan He (2026). *The energy cost of optical noise*. DOI: [10.5281/zenodo.23629201](https://doi.org/10.5281/zenodo.23629201).

*Commentary.*

spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment 1) (fockDensity 0))) = ENNReal.ofReal(Real.log 2). The completed Bargmann kernel computes the beam output as sqrt(1/2)*(tensor e0 e1 - tensor e1 e0). The actual marginal is one half times the sum of the orthogonal occupation-zero and occupation-one rank-one projectors, hence its actual operator A satisfies A*A=(1/2) smul A. The channel bridge and spectral polynomial criterion give equality. The vacuum polynomial is also consumed in the coherent-family proof; the vacuum entropy equality is consumed by the vacuum comparison.

**Theorem 1.3 (Every coherent density attains log two).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_entropy` (`✓ std3`). ∎

*Citation.* Zixuan He (2026). *The energy cost of optical noise*. DOI: [10.5281/zenodo.23629201](https://doi.org/10.5281/zenodo.23629201).

*Commentary.*

For every alpha : Complex, spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment 1) (coherentDensity alpha))) = ENNReal.ofReal(Real.log 2). The actual completed displacement sends e0 to coherent alpha. The existing coherent_output_covariance conjugates the actual vacuum output by displacement (sqrt(1/2)*alpha). This star-algebra conjugation transports A*A=(1/2) smul A to the same actual coherent output. The proved polynomial entropy criterion then gives equality without assuming unitary invariance for another entropy API.

**Theorem 1.4 (Vacuum minimizes over all densities).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_minimizes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_minimizes` (`✓ std3`). ∎

*Citation.* Zixuan He (2026). *The energy cost of optical noise*. DOI: [10.5281/zenodo.23629201](https://doi.org/10.5281/zenodo.23629201).

*Commentary.*

For every Attenuator.DensityOperator rho, the native spectral entropy of the actual vacuum output is at most that of the actual output at rho. Both sides use the same densityReference adapter and balanced one-photon environment. Substitute the proved vacuum equality into the all-density one-photon floor. No restriction is added to rho.

**Theorem 1.5 (Every coherent input minimizes over all densities).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_minimizes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_minimizes` (`✓ std3`). ∎

*Citation.* Zixuan He (2026). *The energy cost of optical noise*. DOI: [10.5281/zenodo.23629201](https://doi.org/10.5281/zenodo.23629201).

*Commentary.*

For every alpha : Complex and every Attenuator.DensityOperator rho, spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment 1) (coherentDensity alpha))) <= spectralEntropy (densityReference (attenuator (1/2) balanced (pointMassEnvironment 1) rho)). Substitute the exact coherent equality into the unconditional one-photon floor. Together with equality this gives the attained minimum log two for the native extended spectral entropy. At other odd occupations only the lower floor is supplied; no further occupation or transmissivity case of the conjecture is settled here.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.attenuator_pureDensity_eq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_entropy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_coherent_minimizes`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_entropy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment.balanced_one_photon_vacuum_minimizes`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedSpectralEntropy](BalancedSpectralEntropy.md)
