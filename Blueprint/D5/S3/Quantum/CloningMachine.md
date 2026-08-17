# Cloning Machine Entropy

## Abstract

The universal symmetric cloning machine has an input-independent machine entropy.

**Theorem 1.1 (The cloning machine entropy has an exact closed form).**

$$\operatorname{machineEntropy} = \operatorname{logb}(2, 3) - \frac{2}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CloningMachine.machine_entropy_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen module first derives that every normalized pure qubit input gives the universal symmetric 1-to-2 cloning machine a reduced-state spectrum of {1/3, 2/3}. The definition machineEntropy packages the binary entropy of those eigenvalues, so it is independent of the input.

Expanding that definition and applying the real logarithm quotient laws gives the exact value logb(2, 3) - 2/3 bits. This declaration proves the closed-form entropy identity only; it does not construct the cloning isometry or strengthen the universal no-cloning theorem.

## References

- Truth anchor: `D5/S3/Quantum/CloningMachine.machine_entropy_closed_form`
