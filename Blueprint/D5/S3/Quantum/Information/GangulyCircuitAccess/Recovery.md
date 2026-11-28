# A circuit-authorized set that cannot recover the secret

## Abstract

A seven-vertex simple graph refutes the inclusion in Ganguly’s Section VI Problem 2.

**Definition 1.1 (Recovery by one CPTP map).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.reconstructs`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.reconstructs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

There exists one completely positive trace-preserving map from matrices on the retained basis to the logical qubit matrices. For every logical complex matrix ρ, applying this map to the reduced encoding of ρ yields ρ. The CStarMatrix conversions only change the Lean carrier.

**Definition 1.2 (Universal inclusion of circuit access in recovery access).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Ganguly, Section VI, Problem 2, p. 22. “For simple graphs Γ, does the condition that Γᶜⁱʳᶜ_{L(Γ),d} is a quantum access structure imply Γᶜⁱʳᶜ_{L(Γ),d} ⊆ Γʳᵉᶜ_d? This holds for at most six vertices (Table I) and fails for graphs with loops (Example 6).” The Lean assertion quantifies over all natural vertex counts, simple graphs on Fin(n) with decidable adjacency, and dealers. Under the quantum access antecedent it requires recovery for every circuit-authorized A using the dealer-slice encoding.

**Theorem 1.3 (Refutation of the universal inclusion).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result` (`✓ std3`). ∎

*Resolves.* `Problems/ganguly-2026-circuit-access-recovery-inclusion` (refuted) by `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ganguly-2026-circuit-access-recovery-inclusion","declaration_gid":"D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The universal inclusion is false. For the seven-vertex graph the circuit family is a quantum access structure and contains {2, 5, 6} at dealer 4. The encoding is the isometry into the shortened code established by the witness correspondence with Proposition 8. The two logical pure inputs have the same retained matrix. A completely positive trace-preserving recovery map would have to map that one matrix to both distinct inputs. This establishes a failure at seven vertices. The smaller-size assertion in the quoted question is attributed to Table I.

## References

- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.claim`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.reconstructs`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial](Combinatorial.md)
- Dependency: [D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding](Encoding.md)
