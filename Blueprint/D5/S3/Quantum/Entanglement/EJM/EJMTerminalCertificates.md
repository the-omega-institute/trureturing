# Literal terminal events, transport witnesses and scaled inequalities

## Abstract

Actual complete-event and integer-comparison premises of the EJM local certificate.

Each numerical terminal check reads the actual complete event and proposed coordinate/outcome witness, checks exact transport to the referenced contraction representative, and verifies the required integer lower-bound comparison. The whole-domain tag checks identify every complete row with its literal terminal event, so a proof cannot silently replace a row's event. Correctness of the stored contraction integer remains a separate premise discharged by EJMContractionCertificates. Terminal-bound soundness combines these premises on the actual original centered score.

**Theorem 1.1 (All 4588 triangle terminal checks).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal triangle complete row passes its actual transport and scaled integer-comparison check. This is a premise of triangle_all_terminal_bounds, consumed together with all actual contraction receipts and the complete-row tag check.

**Theorem 1.2 (All 1192 singleton terminal checks).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every literal singleton complete row passes its transport and integer comparison, retaining the singleton centered-score factor 64. The theorem covers the entire actual terminal domain without assuming an external minimum.

**Theorem 1.3 (The terminal tag of every actual triangle row).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All 41294 triangle row tags are checked. A complete row must have an index in the literal terminal domain and its actual event must equal the indexed terminal event; split rows supply no replacement terminal inequality.

**Theorem 1.4 (The terminal tag of every actual singleton row).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding check covers all 8689 singleton row tags, identifying every complete row's original event before its terminal inequality is transported into full local acceptance.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_tags`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.singleton_terminals`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_tags`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalCertificates.triangle_terminals`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData](EJMTerminalBoundData.md)
