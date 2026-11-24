# The five-dimensional computational and Fourier score threshold

## Abstract

The combined triangular discrimination of the computational and Fourier measurement outcomes is less than 377/100 for any two complex unit vectors in dimension five.

**Definition 1.1 (The two-basis score).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore`

*Formalization.* `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Acknowledgement.* Anonymous (2026). *Sharp qutrit discrimination and unavoidable correlation overcounting for complementary measurements*. DOI: [10.5281/zenodo.23933731](https://doi.org/10.5281/zenodo.23933731). URL: <https://doi.org/10.5281/zenodo.23933731>.

*Commentary.*

Qian's Eq. (9) gives the score for the two-ray family in Eq. (8). Sum (p−q)²/(p+q) over the computational and normalized positive Fourier outcome tables. A common zero row contributes zero.

**Theorem 1.2 (The radical upper bound).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_le_radical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_le_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Acknowledgement.* Anonymous (2026). *Sharp qutrit discrimination and unavoidable correlation overcounting for complementary measurements*. DOI: [10.5281/zenodo.23933731](https://doi.org/10.5281/zenodo.23933731). URL: <https://doi.org/10.5281/zenodo.23933731>.

*Commentary.*

Write A = 1 − √((5 + √5)/10) and E = 1 − √((7 + √5)/10). The Gram compression bounds give the two mask gaps, so every pair of unit vectors satisfies S ≤ 4 − 8E + 8E²/A. Simultaneous conjugation transports the inverse Fourier coordinates to the positive Fourier convention.

**Theorem 1.3 (Qian §11(3), the strict threshold).**

Lean statement: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_lt_377_div_100`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_lt_377_div_100` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Acknowledgement.* Anonymous (2026). *Sharp qutrit discrimination and unavoidable correlation overcounting for complementary measurements*. DOI: [10.5281/zenodo.23933731](https://doi.org/10.5281/zenodo.23933731). URL: <https://doi.org/10.5281/zenodo.23933731>.

*Commentary.*

The radical bound gives D ≥ 53682/933125 > 23/400 for the harmonic deficit and S = 4 − 4D. Thus S < 377/100 for every pair of unit vectors. The orthonormal pairs in Qian §11(3) meet these hypotheses.

Qian Theorem 6.14 exhibits an orthonormal pair with S = (14 + 2√5)/5. Qian's witness supplies an attained lower bound on the maximum. The sharp maximum remains open. The separately deposited qutrit certificate at Zenodo DOI 10.5281/zenodo.23933731 establishes the sharp dimension-three bound and leaves the dimension-five upper bound open.

## References

- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_le_radical`
- Truth anchor: `D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold.positiveFourierScore_lt_377_div_100`
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveBasis](FourierFiveBasis.md)
- Dependency: [D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound](FourierFiveCrossBound.md)
