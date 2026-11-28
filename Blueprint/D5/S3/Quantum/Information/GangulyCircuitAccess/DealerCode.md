# The dealer-shortened stabilizer code for the witness

## Abstract

The normalized graph-state slices give an isometry onto the common fixed space of the shortened lift.

**Definition 1.1 (Player configurations).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.WitnessPlayers`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.WitnessPlayers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The player basis is the product of the discarded and retained configuration types, in that order.

**Definition 1.2 (Lift of the binary adjacency labels).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.graphPauli`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.graphPauli` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For x and z in Bits(7), apply the translation ψ(z+x) and multiply by the sign with binary exponent q(x) + (Mx)·z. Here q is the quadratic graph phase. This is the Pauli with label (x,Mx), in output phase order Z(Mx)X(x), multiplied by the sign of q(x).

**Definition 1.3 (Graph-state amplitudes).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessGraphState`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessGraphState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

At z in Bits(7), take the graph sign divided by the square root of 128, in the complex numbers.

**Definition 1.4 (Player operator of a shortened label).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.shortenedPauli`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.shortenedPauli` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Apply the graph Pauli to the player wave function pulled back by restriction to player coordinates, and evaluate at the joint configuration with dealer bit zero. The shortening uses labels x with x(4) = (Mx)(4) = 0.

**Definition 1.5 (The shortened fixed space).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessShortenedCode`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessShortenedCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The code consists of all player vectors fixed by every shortened Pauli whose two dealer coordinates vanish.

**Theorem 1.6 (Witness correspondence with Proposition 8(2–3)).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witness_proposition8`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witness_proposition8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The lifted operators compose by addition of their binary labels. A full vector fixed by every lift is exactly a scalar multiple of the graph state. For every label with both dealer coordinates zero and every player vector, the lifted operator on that vector is independent of the dealer bit and agrees with the shortened player operator. Every joint graph-state amplitude is the corresponding slice entry divided by √2. The dealer marginal has entries obtained by summing each amplitude times the conjugate amplitude at the other dealer bit over all player configurations, and equals I/2. The slice matrix satisfies V†V = I and its image equals the whole shortened fixed space. Multiplying a player amplitude by its zero-dealer graph sign makes it constant on each of the two dealer-parity classes. Both classes occur by dealer surjectivity. The two columns span the resulting functions, with relative sign +1 on one class and −1 on the other.

## References

- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.WitnessPlayers`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.graphPauli`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.shortenedPauli`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessGraphState`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witnessShortenedCode`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.witness_proposition8`
- Dependency: [D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial](Combinatorial.md)
- Dependency: [D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding](Encoding.md)
