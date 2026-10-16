# ProbeComponentRigidity

## Abstract

Universal density-input probability preservation forces scalar Kraus action on the complex span of each nonorthogonality component.

Let unit complex vectors form an arbitrary index family in a finite dimensional Hilbert space. Nonzero overlap generates an equivalence relation. Each class determines the span of all probes in that class. Probability preservation is required for every density input, rather than only an individual input state. The dual map fixes every probe projection. Expanding the positive sum of squared Kraus commutators forces each commutator to vanish. The scalar actions agree across nonzero overlaps, extend along finite chains, and then extend linearly over the whole component. Mayer and Knill Theorem 1 gives the connected rigidity statement; Koashi and Imoto give broader nondisturbance structure.

**Theorem 1.1 (kraus normalized of channel).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_normalized_of_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_normalized_of_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andreas Bluhm, Lukas Rauber, and Michael M. Wolf (2018). *Quantum compression relative to a set of measurements*. URL: <https://arxiv.org/html/1708.04898v4>.

*Commentary.*

Trace preservation of a canonical rectangular channel implies adjoint-Gram normalization for every finite Kraus representation. The channel scalarity and canonical flagged-port factorization consume this supplier.

**Theorem 1.2 (probability preserving kraus commute).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.probability_preserving_kraus_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.probability_preserving_kraus_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

For every normalized finite Kraus representation preserving each probe probability on all density inputs, every Kraus matrix commutes with every probe projection.

**Theorem 1.3 (kraus scalar on component).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_scalar_on_component`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_scalar_on_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

For every Kraus index, every probe index, and every vector in its component span, the Kraus action equals a scalar times that vector. The scalar is the unit probe expectation of that Kraus matrix. No finiteness assumption is imposed on the probe family.

**Theorem 1.4 (channel component scalar).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.channel_component_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.channel_component_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

Every canonical completely positive trace-preserving channel satisfying the probability equations has a rectangular finite Kraus representation whose normalization and scalar action on every component are proved.

**Theorem 1.5 (connected probability preserving identity).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

If the unit probe family spans the full space and every pair belongs to the same component, its probability-preserving Kraus channel equals identity on every complex matrix. Every Kraus matrix is a scalar identity. A probe index and an ambient basis index explicitly provide the nonempty interfaces.

**Theorem 1.6 (component stinespring form).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.component_stinespring_form`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeComponentRigidity.component_stinespring_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Acknowledgement.* Masato Koashi and Nobuyuki Imoto (2002). *Operations that do not disturb partially known quantum states*. URL: <https://arxiv.org/abs/quant-ph/0101144>.

*Commentary.*

For each component the finite environment coefficients have squared norm one. Every vector in the component maps to its original system coordinates multiplied by the same environment coefficients. The coordinates are the actual Kraus Stinespring coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.channel_component_scalar`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.component_stinespring_form`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.connected_probability_preserving_identity`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_normalized_of_channel`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.kraus_scalar_on_component`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeComponentRigidity.probability_preserving_kraus_commute`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausLeftInverseNecessity](../Recovery/KrausLeftInverseNecessity.md)
