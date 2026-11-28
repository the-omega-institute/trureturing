# Unequal-temperature CAR coherence

## Abstract

Two CAR modes at unequal inverse temperatures can exceed both single-mode rank-one gains.

**Theorem 1.1 (The hole lowering matrices).**

Lean statement: `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.car`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

In empty, first, second, both hole order, the first matrix has unit entries at (0,1) and (2,3). The second has entries 1 at (0,2) and −1 at (1,3). All other entries vanish. Each is the adjoint of the corresponding occupation lowering matrix reindexed by complementing both occupation bits and putting the first hole bit second in the product index. Their products Jᵢ†Jᵢ project onto the states with hole i present. For a unit vector x, the expectation zᵢ = x†Jᵢx is the conjugate of the occupation lowering expectation in the reindexed state, so their squared moduli agree.

**Theorem 1.2 (Exact witness and axis optima).**

Lean statement: `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.physical_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.physical_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

At source exponent two, take β = 8 log 2 and the two mode parameters (4 log 2, 8 log 2). Equations (3.54) and (3.55) of Wu v1 give α₂*(β) = 2L. Set aᵢ = 1/(1+exp βᵢ), bᵢ = 1−aᵢ and T = Tr(M²) for the Gibbs-embedded positive input M. On the rank-one density M²/T, the two transported jump traces for mode i both equal |zᵢ|². Its contribution to the entropy divided by T is −log bᵢ + βᵢqᵢ. Subtracting the entropy term from the energy gives the deficit divided by 2T as ∑ᵢ(aᵢ + L log bᵢ) − ∑ᵢ(cᵢ|zᵢ|² − dᵢqᵢ). This identity uses the continuous extension to rank-one positive inputs. With L = (cosh(β/2) − 1)/(β sinh(β/2)), the coefficients cᵢ = sech(βᵢ/2) and dᵢ = tanh(βᵢ/2) − L βᵢ are (8/17, 32/257) and (15/34, 480/4369), respectively. The unit vector (60,9,10,1)/√3782 has hole probabilities (82,101)/3782 and lowering expectations (550,591)/3782. Its total gain ∑ᵢ(cᵢ|zᵢ|² − dᵢqᵢ) is 15416747/31246048178 > 49/100000. For each mode, |zᵢ|² ≤ qᵢ(1 − qᵢ) by Cauchy–Schwarz. A superposition of the hole vacuum and the corresponding one-hole vector attains equality at qᵢ = (cᵢ − dᵢ)/(2cᵢ). Completing the square gives the exact maxima 1/2176 and 32/74273.

**Theorem 1.3 (Failure of single-mode domination).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The claim asks whether for each unit vector there is a mode and a unit vector whose gain on that mode alone dominates the original total gain. Both single-mode maxima lie below 49/100000, so the exhibited unit vector refutes the claim at these two unequal temperatures.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.car`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.physical_certificate`
- Truth anchor: `D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.result`
- Dependency: [D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison](../Semigroups/TwistedTwoModeOUComparison.md)
