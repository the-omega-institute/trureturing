# Completed antisymmetry and the odd-occupation half cap

## Abstract

Odd Fock occupation at balance imposes a half-identity cap on every density output.

The balanced one-photon all-density spectral minimum and attainment by every coherent input are already proved in `D5/L/Entropy/he2026energy`, Theorem 2 (PDF page 5) and Appendix A.2-A.3 (PDF pages 18-19). This attributed formalization preserves that physical result. No new literature resolution or priority for the odd-occupation application is claimed.

All spaces and operators are the existing FockAttenuator objects. Fock is lp (fun _ : Nat => Complex) 2 and TwoMode is lp (fun _ : Nat => Fock) 2. V j is the retained-mode column indexed by discarded occupation j; its retained coefficient at i is V j i. tensor u a has column a(j) times u. The identity is the bounded identity on the full completed Fock space, the order is Mathlib Loewner order, and the scalar is the complex embedding of the real one half.

The paper states Conjecture 1 for pure number-state environments at every transmissivity and occupation. Here transmissivity is exactly one half. Every odd occupation has an output cap; no attainer for odd n greater than one, other transmissivity, or even-occupation bound is asserted. BalancedAttainment supplies the one-photon spectral minimum. These are repo-derived arguments on the actual physical APIs, with the paper acknowledged for its problem and convention and no literature priority claim.

**Theorem 1.1 (The balanced parameter is admissible).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The real parameter one half belongs to the closed interval from zero to one. This proof is consumed as the admissibility argument of the actual beamSplitter and attenuator throughout these modules. This follows from the rational inequalities 0 <= 1/2 and 1/2 <= 1.

**Theorem 1.2 (The actual completed output is skew).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_skew`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every completed Fock x, every natural n with Odd n, and all i and j, the actual V = beamSplitter (1/2) balanced (tensor x (lp.single 2 n 1)) satisfies V i j = -V j i. No unit-norm or support assumption is needed. kernel_beam_unitary and transform_single give kernel(V)(z,w) = transform(x)(sqrt(1/2)*(z+w)) * (sqrt(1/2)*(w-z))^n/sqrt(n!). Swapping z and w preserves the sum coordinate and negates the odd difference factor. Square-summability and Parseval construct the swap isometry on the completion; kernel_swap and kernel_injective then identify the vector. This parity helper is consumed by the all-density cap.

**Theorem 1.3 (The completed contraction-wedge estimate).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_quadratic_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_quadratic_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every completed TwoMode V satisfying V i j = -V j i and every Fock u, Re inner(u,purePartialTrace V u) <= (norm(V)^2/2)*norm(u)^2. Put a(j)=inner(u,V j). Square-summability makes a an actual Fock vector. pure_partial_trace_eq and adjoint_coefficient identify the quadratic form with norm(a)^2. The wedge tensor u a - tensor a u has squared norm at most 2*norm(u)^2*norm(a)^2; its inner product with V is 2*norm(a)^2. Cauchy-Schwarz, with a separate zero-contraction branch, yields the factor one half without a finite truncation. This estimate is consumed in the physical density-ensemble proof.

**Theorem 1.4 (The actual marginal in Loewner order).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every completed skew V, purePartialTrace V <= ((norm(V)^2/2 : Real) : Complex) smul identity. Positivity follows from the existing purePartialTrace V = coefficientOperator V * star(coefficientOperator V). The preceding quadratic estimate proves positivity of the difference from the scalar identity. These are the actual completed coefficient operator, adjoint and partial trace; no finite matrix or assigned spectrum replaces them.

**Theorem 1.5 (The half cap for every actual density input).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_attenuator_le_half`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_attenuator_le_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every n : Nat with Odd n and every Attenuator.DensityOperator rho, attenuatorOperator (1/2) balanced (pointMassEnvironment n) rho <= ((1/2 : Real) : Complex) smul identity. In particular n=1 is a direct specialization. The original outputVector uses sqrt(rho)e_m. Their squared norms have HasSum one by the positive square-root identity and trace_one. The point-mass environment removes the other environment indices. Norm-summability permits the continuous quadratic form to pass through the original rank-one mixture. Applying the skew marginal estimate to each completed physical output and summing gives the cap. No support, rank, energy, input-purity or finite-entropy premise is imposed.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_le`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.antisymmetric_partial_trace_quadratic_le`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_attenuator_le_half`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap.balanced_odd_skew`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel](CompletedKernel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteRankClassification](FiniteRankClassification.md)
