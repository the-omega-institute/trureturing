# The original complete row remains the object of every terminal check

## Abstract

Actual EJM terminal events, proposed transport witnesses and executable checks.

The data stores one proposed coordinate/outcome action and contraction-representative index for each of the 4588 triangle and 1192 singleton terminal events. Terminal events are decoded from the original local row data, while proposed witnesses come from separate literal integer dictionaries. The check definitions test exact event identity, exact tail transport and the scaled lower-bound comparison. Defining these checks does not prove they return true. All terminal checks and every row tag require complete kernel acceptance receipts, and all proposed contraction integers require their separate original-function equalities before terminal-bound soundness yields a centered-score inequality.

**Definition 1.1 (Read the hash from either original raw row constructor).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.rawHash`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.rawHash` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same hash field is returned from a terminal or branch raw row. This field is data; its relationship to a complete-row rule is checked by the terminal and tag consumers.

**Definition 1.2 (The actual triangle terminal event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalEvent`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index in Fin 4588, the event comes from the hash of the corresponding original ten-coordinate triangle raw row, using the original total event decoder.

**Definition 1.3 (The actual proposed triangle transport witness).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The stored integer is decoded into a local action and a Fin 95 contraction representative. These are untrusted proposals until the exact tail equality is checked.

**Definition 1.4 (Executable triangle terminal acceptance test).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalCheck`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A split rule rejects. A complete rule checks that its original event equals the decoded terminal event, that its seven-tail transforms exactly to the proposed contraction representative, and that its actual scaled lower bound is at most 256 times F1 at that event minus the proposed contraction integer. Correctness of that contraction integer is a separate premise.

**Definition 1.5 (Executable triangle complete-event tag check).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalTagCheck`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalTagCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every complete row must have an index below 4588 and its actual event must equal the corresponding literal terminal event. A split row returns true because this tag check asserts no terminal inequality for it.

**Definition 1.6 (The actual singleton terminal event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalEvent`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index in Fin 1192, the event is decoded from the corresponding original nine-coordinate singleton raw row.

**Definition 1.7 (The actual proposed singleton transport witness).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal witness dictionary decodes into an actual local action and a Fin 332 contraction representative. The downstream checker, rather than the producer, establishes the exact tail match.

**Definition 1.8 (Executable singleton terminal acceptance test).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalCheck`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The check retains original complete-event identity and exact eight-tail transport. Its integer comparison is the actual row lower bound at most 256 times F2 minus 64 times the proposed contraction integer, preserving the singleton centered-score factor.

**Definition 1.9 (Executable singleton complete-event tag check).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalTagCheck`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalTagCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every singleton complete row must lie in the first 1192 rows and equal its decoded terminal event. This whole-row tag test supplies an exact event-identification premise; it does not itself validate a numerical bound.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.rawHash`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalCheck`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalEvent`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonTerminalTagCheck`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.singletonWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalCheck`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalEvent`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleTerminalTagCheck`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.triangleWitness`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMContractionData](EJMContractionData.md)
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport](EJMPartialBoundTransport.md)
