# Finite Edge Record Laws

## Abstract

Independent fair edge and site bits give uniform output laws on every proper subset of an open path.

**Theorem 1.1 (The all-ones input selects a parity class).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_allOn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_allOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

On a path with N = n + 1 sites, each active site outputs the XOR of the two adjacent edge bits, with zero at missing edges and a shift by b at site zero. An inactive site outputs its own fair bit. Prefix XOR, after removing the endpoint shift, recovers the edge bits from the full parity word. The all-ones row is uniform on parity b. Every other row is uniform on all words. The underlying adjacent XOR parity sampler appears in Horacsek et al., Local Samplers for Product Distributions, Section 1.

**Theorem 1.2 (Every proper output law is uniform for every input).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zidu Liu and Dominik S. Wild (2026). *Efficiently Learning Global Quantum Channels with Local Tomography*. DOI: [10.1103/51mt-ghpn](https://doi.org/10.1103/51mt-ghpn). URL: <https://arxiv.org/abs/2603.07037v1>.

*Commentary.*

For a proper site mask, fixing the visible coordinates of a parity word leaves one unseen coordinate available to enforce parity. All fibers therefore have the same size. Inactive coordinates contribute independent fair bits.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_allOn`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw.kernel_marginal`
