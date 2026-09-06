# Environment Records and Selected Fixed Entries

## Abstract

Tracing controlled qubit records gives phase damping under the stated Gram condition, and unit overlaps characterize the record-channel fixed points.

Let r be a function from Fin(2) to Fin(2) to the complex numbers, and let rho be an arbitrary complex two-by-two matrix. The record overlap G is the sum of r(i,a) times the complex conjugate of r(j,a), over the two environment indices a. The controlled joint matrix has entry r(i,a) times the conjugate of r(j,b) times rho(i,j) at indices (i,a),(j,b). The environment trace sums the entries at (i,a),(j,a).

**Theorem 1.1 (A prescribed record Gram matrix yields phase damping).**

$$\forall r:\operatorname{Fin}\left(2\right)\to\operatorname{Fin}\left(2\right)\to\mathbb{C},\ \forall \rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\ \forall c \in [0,1],\ (\forall i, j \in \operatorname{Fin}\left(2\right),\ \operatorname{recordOverlap}\left(r, i, j\right) = \operatorname{if}\left(i = j, 1, c\right)) \Rightarrow \operatorname{traceEnvironment}\left(\operatorname{controlledRecordJointState}\left(r, \rho\right)\right) = \operatorname{phaseDamping}\left(c, \rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords.trace_environment_controlled_record_eq_phase_damping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

Let c be a DampingCoefficient, so its real value lies in [0,1]. Suppose, for every i and j in Fin(2), that G(i,j) equals one when i = j and the complex cast of c otherwise. Then tracing the environment out of controlledRecordJointState(r,rho) equals phaseDamping(c,rho). The Gram premise includes unit norm for each record. No positivity, Hermiticity, or trace-one condition is imposed on rho.

Entrywise, the finite environment sum factors as G(i,j) times rho(i,j). Substitution of the Gram premise preserves diagonal entries and multiplies every off-diagonal entry by c. Zurek's review supplies the environment-overlap interpretation; this identity is derived from the explicitly defined finite record interaction and assumes the stated overlaps.

**Theorem 1.2 (Unit record overlaps select the fixed entries).**

$$\forall r:\operatorname{Fin}\left(2\right)\to\operatorname{Fin}\left(2\right)\to\mathbb{C},\ \forall \rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\ \operatorname{recordChannel}\left(r, \rho\right) = \rho \iff (\forall i, j \in \operatorname{Fin}\left(2\right),\ \operatorname{recordOverlap}\left(r, i, j\right) \ne 1 \Rightarrow \rho_{ij} = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords.record_channel_fixed_iff_selected_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wojciech H. Zurek (2003). *Decoherence, einselection, and the quantum origins of the classical*. DOI: [10.1103/RevModPhys.75.715](https://doi.org/10.1103/RevModPhys.75.715).

*Commentary.*

For every record r and every qubit matrix rho, recordChannel(r,rho) = rho if and only if, for all i and j, G(i,j) different from one implies rho(i,j) = 0. Here recordChannel acts entrywise by multiplication by G. This theorem does not assume the preceding Gram condition or normalized records; the condition also applies to diagonal entries when G(i,i) is not one.

The fixed-point equation at an entry is (G(i,j) - 1) times rho(i,j) = 0. Since the complex numbers have no zero divisors, an overlap different from one forces that entry to vanish. Conversely, the vanishing condition makes multiplication by G fix every entry. An interpretation as blocks of identical normalized records requires the corresponding normalization assumptions separately.

## References

- Truth anchor: `D5/S3/Quantum/EnvironmentRecords.record_channel_fixed_iff_selected_blocks`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords.trace_environment_controlled_record_eq_phase_damping`
- Dependency: [D5/S3/Quantum/PointerBasis](PointerBasis.md)
