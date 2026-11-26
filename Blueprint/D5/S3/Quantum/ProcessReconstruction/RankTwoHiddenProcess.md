# Kraus Rank and Hidden Process Correlations

## Abstract

For a register of at least two qubits, the minimal Kraus rank for ambiguity from all proper output channels is two.

**Theorem 1.1 (Proper-output reconstruction for rank-one channels).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.one_kraus_eq_of_proper_output_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.one_kraus_eq_of_proper_output_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Schumacher and Reinhard F. Werner (2004). *Reversible Quantum Cellular Automata*. DOI: [10.48550/arXiv.quant-ph/0405174](https://doi.org/10.48550/arXiv.quant-ph/0405174). URL: <https://arxiv.org/abs/quant-ph/0405174v1>.

*Acknowledgement.* Erkka Haapasalo, Teiko Heinosaari and Juha-Pekka Pellonpää (2012). *When do pieces determine the whole? Extremal marginals of a completely positive map*. DOI: [10.48550/arXiv.1209.5933](https://doi.org/10.48550/arXiv.1209.5933). URL: <https://arxiv.org/abs/1209.5933v1>.

*Commentary.*

A single Kraus operator for a trace-preserving channel on an equal finite input and output basis is unitary. For a register with at least two sites, the proper output channels include all single-site outputs. Their equality determines the global channel when both channels have a single Kraus operator.

**Theorem 1.2 (Rank-two channels with identical complete proper outputs).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.rank_two_ambiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.rank_two_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Schumacher and Reinhard F. Werner (2004). *Reversible Quantum Cellular Automata*. DOI: [10.48550/arXiv.quant-ph/0405174](https://doi.org/10.48550/arXiv.quant-ph/0405174). URL: <https://arxiv.org/abs/quant-ph/0405174v1>.

*Commentary.*

Two unital channels retain the same two diagonal blocks, and one channel changes the sign of the coherence between the all-zero and all-one basis words. A proper partial trace kills both of the matrix units carrying the difference for every input matrix. The proper output channels remain equal under every finite reference amplification.

The balanced superposition of those words gives orthogonal outputs, attaining unhalved diamond distance two. Another pure input gives an output of rank two for each channel, so each two-Kraus representation is minimal.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.one_kraus_eq_of_proper_output_eq`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess.rank_two_ambiguity`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/ParityFamily](ParityFamily.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/SwapReconstruction](SwapReconstruction.md)
