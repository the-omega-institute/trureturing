# Writing two records with local baths and joint permutations

## Abstract

A sharp bath variation budget for writing two classical records with joint reversible gates.

**Theorem 1.1 (The permutation-invariant range).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.potential_eq_twice_range`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegister.potential_eq_twice_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

The maximum of the three pairwise sums of absolute Walsh moments equals twice the range of the four joint masses. Pairwise mass differences give both relative signs for each pair of moments.

**Theorem 1.2 (Variation controls the increase during a local bath).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.firstBath_potential_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegister.firstBath_potential_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

The bath on the first bit preserves the second bit's signed moment. It interpolates the parity moment toward the product of that preserved moment and the reset bias. This bounds the increase in the potential by twice the total variation of the joint law across the contact.

**Theorem 1.3 (The two marginal contrasts require bath variation).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

Both event branches start uniform on the same two-bit register. Each branch permits any finite sequence of joint permutations and independent single-bit relaxation steps. The sum of the total variation distances between the two final single-bit marginals is at most the sum of the bath variations in the two branches. Joint permutations preserve the range of the masses even when the permutation depends on the event. For a uniform event, each marginal distance is one minus twice its Bayes decoding error. This is the finite transport step for the collective extension posed after Equation (7) in Chung's Section VIII.

**Theorem 1.4 (Two resets attain the bath variation bound).**

Lean statement: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wonyong Chung (2026). *The thermodynamic budget of objectivity*. URL: <https://arxiv.org/abs/2611.34909v1>.

*Commentary.*

For any two target contrasts in the unit interval, reset one bit at a time to independent laws of those biases. Complement both bits in one event branch at the end. The two marginal contrasts equal the prescribed values and the two branch variations sum to their sum.

## References

- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.firstBath_potential_le`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.potential_eq_twice_range`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound`
- Truth anchor: `D5/S3/Quantum/Information/RecordWriting/TwoRegister.recording_bound_sharp`
- Dependency: [D5/S3/TotalVariation/Pinsker](../../../TotalVariation/Pinsker.md)
