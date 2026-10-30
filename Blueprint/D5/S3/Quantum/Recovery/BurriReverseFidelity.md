# The physical channel with its identity reference

## Abstract

Entanglement fidelity of the actual reverse-instance composite channels.

**Theorem 1.1 (The canonical reference density).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseFidelity.canonical_reference_purification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseFidelity.canonical_reference_purification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximally entangled vector is exactly the vectorized positive square root of rho = I/2. Its rank-one density is positive, has trace one, and has the required reference marginal.

**Theorem 1.2 (The actual tensor extension).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseFidelity.tensor_reference_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseFidelity.tensor_reference_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The channel acts on the first factor, and the reference is the second. Applying the actual channel to each reference-indexed matrix block is exactly the Kraus action by K tensor I. Thus the purified overlap is the squared-fidelity convention for a pure canonical reference.

**Theorem 1.3 (The actual recovered purification).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_recovered_purification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_recovered_purification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the actual decoder channel with the actual physical noise channel and adjoining the identity reference gives exactly the previously calculated recovered purification, retaining all pairs of environment labels.

**Theorem 1.4 (The strict reverse comparison).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For this fixed explicit instance, the source-row composite has strictly smaller entanglement fidelity than the ordinary reference-completed Petz composite. The Petz value is 27/31. The strictness follows from the exact radical sum-of-squares gap. This is a single reverse instance; no joint theorem about both directions is asserted.

**Theorem 1.5 (Every positive-polar completion loses strictly).**

Lean statement: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity_all_completions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity_all_completions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full complex coisometry Uprime with M Uprime positive semidefinite, the literal prepared source Kraus rows define a channel whose entanglement fidelity is strictly below ordinary Petz. This follows from equality of the actual supported action, without fixing an arbitrary null-space rotation.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_recovered_purification`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseFidelity.actual_strict_fidelity_all_completions`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseFidelity.canonical_reference_purification`
- Truth anchor: `D5/S3/Quantum/Recovery/BurriReverseFidelity.tensor_reference_kraus`
- Dependency: [D5/S3/Quantum/Recovery/BurriReverseCompletion](BurriReverseCompletion.md)
