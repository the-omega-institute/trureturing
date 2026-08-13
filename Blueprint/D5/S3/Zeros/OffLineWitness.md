# Off-Line Witness

## Abstract

A closed off-line zero refutes the universal midline claim.

**Theorem 1.1 (A closed off-line zero refutes universal midline location).**

$$\forall x0 \in \left(\forall x0 \in \mathrm{Complex},\; \mathrm{Type}\right),\; \forall x1 \in \left(\forall x1 \in \mathrm{Complex},\; \mathrm{Type}\right),\; \forall x2 \in \mathrm{Real},\; \forall x3 \in \mathrm{Complex},\; \forall x4 \in \mathit{x0}\left(\mathit{x3}\right),\; \forall x5 \in \mathit{x1}\left(\mathit{x3}\right),\; \mathrm{re}\left(\mathit{x3}\right) \ne \mathit{x2} \Rightarrow \left(\neg \left(\forall x7 \in \mathrm{Complex},\; \forall x8 \in \mathit{x0}\left(\mathit{x7}\right),\; \forall x9 \in \mathit{x1}\left(\mathit{x7}\right),\; \mathrm{re}\left(\mathit{x7}\right) = \mathit{x2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/OffLineWitness.closed_zero_midline_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source atom says that a closed-zero-only-on-the-midline claim is false when its instrument supplies an off-line closed zero. This partial closure isolates exactly that logical clause: a supplied zero, its closure witness, and its off-line real part contradict the universal location assertion.

The declaration is general over the zero predicate, closure predicate, and proposed midline. It constructs no analytic zero and assumes no properties beyond the three displayed witness hypotheses.

The source's separate necessity claim about multiplicativity or derived positivity is not formalized here and remains unresolved. Pinned Mathlib contained the generic negation lemmas but no closed-zero midline theorem; the proof specializes the disputed universal claim to the supplied witness.

## References

- Truth anchor: `D5/S3/Zeros/OffLineWitness.closed_zero_midline_refutation`
