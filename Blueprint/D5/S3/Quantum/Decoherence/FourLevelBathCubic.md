# A guarded cubic for exact fixed-bath pinching

## Abstract

The exact fixed-bath pinching criterion and two Gibbs laws below the one-third cap.

**Theorem 1.1 (The scalar criterion at the prescribed Gibbs law).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.fixed_bath_pinching_iff_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathCubic.fixed_bath_pinching_iff_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Acknowledgement.* Grzegorz Rajchel; Adam Gąsiorowski; Karol Życzkowski (2018). *Robust Hadamard Matrices, Unistochastic Rays in Birkhoff Polytope and Equi-Entangled Bases in Composite Spaces*. DOI: [10.1007/s11786-018-0384-y](https://doi.org/10.1007/s11786-018-0384-y). URL: <https://arxiv.org/abs/1804.10715v2>.

*Commentary.*

At fixed injective E and finite real β, write p for the Gibbs law. The operation exists exactly if every p(b) ≤ 1/3 and there is one 0 < t ≤ 1 satisfying (1 − 2p(b))²t ≥ (4p(b) − 1)² for all b and phaseCubic(p,t) = 0. The parameter t is the squared spectral gap of a real complementary frame.

The scalar supplier uses the fixed-diagonal pure-state problem. Completing the three columns gives the repeated-column unistochastic slice [p,p,p,1−3p]. Korzekwa et al., Lemma 5, Eq. (19) and Appendix C.3, relate this slice to distinguishability and apply Haagerup's order-four test, described in Appendix A of Rajchel, Gąsiorowski and Życzkowski.

**Theorem 1.2 (An exact realization below the cap).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.feasible_fixed_bath_example`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathCubic.feasible_fixed_bath_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

For each β > 0 choose the distinct energies matching (29, 27, 25, 19)/100. The cubic changes sign between 1/2 and 1 with all guards satisfied on that interval. One energy-conserving unitary for that bath pinches all qutrit density inputs.

**Theorem 1.3 (An obstruction strictly below the cap).**

Lean statement: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.infeasible_fixed_bath_example`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FourLevelBathCubic.infeasible_fixed_bath_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Acknowledgement.* Korzekwa, Kamil; Czachórski, Stanisław; Puchała, Zbigniew; Życzkowski, Karol (2019). *Distinguishing classically indistinguishable states and channels*. DOI: [10.1088/1751-8121/ab30f7](https://doi.org/10.1088/1751-8121/ab30f7). URL: <https://arxiv.org/abs/1812.09083v3>.

*Commentary.*

For each β > 0 choose the distinct energies matching (19999, 15001, 12000, 13000)/60000. Every weight is strictly below 1/3 and the cubic is positive for every t > 0. At that fixed bath, every permitted unitary fails to pinch at least one density input.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.feasible_fixed_bath_example`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.fixed_bath_pinching_iff_cubic`
- Truth anchor: `D5/S3/Quantum/Decoherence/FourLevelBathCubic.infeasible_fixed_bath_example`
- Dependency: [D5/S3/Quantum/Decoherence/FourLevelBathPhysical](FourLevelBathPhysical.md)
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic](../Measurements/ThreeDistinguishabilityCubic.md)
