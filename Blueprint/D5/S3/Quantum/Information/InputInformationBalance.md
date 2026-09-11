# Input Information Balance

## Abstract

The information shared by a reference with two complementary outputs sums to twice the reference entropy when the joint state is pure.

All carriers are finite. IsPure means that the density matrix is the outer product of one amplitude vector with its conjugate. Normalization and positivity belong to DensityState.

**Theorem 1.1 (Complementary marginals have equal entropy).**

$$\forall \rho, \operatorname{IsPure}\left(\rho\right) \Rightarrow \operatorname{vonNeumannEntropy}\left(\operatorname{marginalLeft}\left(\rho\right)\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/InputInformationBalance.pure_complementary_entropy` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2025). *Quantum notions of information and entropy — complementary pure-state marginals*. URL: <https://github.com/leanprover-community/physlib/blob/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/QuantumInfo/Entropy/VonNeumann.lean>.

*Commentary.*

For a pure state on A times B, the coefficient matrix gives the two marginals as rectangular Gram products, with one transposed. Their nonzero eigenvalues agree with multiplicity; zero eigenvalues contribute zero to entropy.

For a global state on A times (B times R), stateAB traces out R after regrouping as (A times B) times R. stateAR traces out B after regrouping as (A times R) times B. The proof identifies the A marginals of both states with marginalRight of the global state, and identifies their B and R marginals with the corresponding complementary cuts.

**Theorem 1.2 (The input information balance).**

$$\forall \rho, \operatorname{IsPure}\left(\rho\right) \Rightarrow \operatorname{quantumMutualInformation}\left(\operatorname{stateAR}\left(\rho\right)\right) + \operatorname{quantumMutualInformation}\left(\operatorname{stateAB}\left(\rho\right)\right) = 2 \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/InputInformationBalance.input_information_balance` (`✓ std3`). ∎

*Citation.* Alex Meiburg (2025). *Quantum notions of information and entropy — complementary pure-state marginals*. URL: <https://github.com/leanprover-community/physlib/blob/889c09c66fb5f3c4a27182a43cafbed9e00b9d0a/QuantumInfo/Entropy/VonNeumann.lean>.

*Commentary.*

Purity gives S(AR) = S(B) and S(AB) = S(R). Expanding I(A:R) and I(A:B) cancels the B and R entropy terms, leaving twice S(A). The theorem takes the final pure joint state as input, including pure states obtained from a pure input and reference by an isometry.

## References

- Truth anchor: `D5/S3/Quantum/Information/InputInformationBalance.input_information_balance`
- Truth anchor: `D5/S3/Quantum/Information/InputInformationBalance.pure_complementary_entropy`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
