# CIRPT Semantic Integrity

## Abstract

Constant observations and full-domain primitives preserve CIRPT semantic integrity.

**Definition 1.1 (Constant CUT bundle).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constantCutBundle`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constantCutBundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each finite index is assigned the CUT kernel of a constant readout.

**Theorem 1.2 (Closed truth has a universal kernel).**

$$\forall X, B, c, x, y, \operatorname{relation}(\operatorname{cutKernel}(\lambda z, c), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.closed_truth_readout_has_universal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair has equal values under a constant readout.

**Theorem 1.3 (Constant CUT bundles agree universally).**

$$\forall X, I, B, v, x, y, \operatorname{agrees}(\operatorname{constantCutBundle}(v), x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constant_cut_bundle_has_universal_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinatewise universality makes the joint bundle relation universal.

**Definition 1.4 (Atom insertion).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.bundleWithAtom`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.bundleWithAtom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An Option index inserts one atom while retaining every old atom index.

**Theorem 1.5 (ADMIT is its Boolean CUT).**

$$\forall X, A, \operatorname{admitKernel}(A) = \operatorname{cutKernel}(\lambda x, \operatorname{decide}(\operatorname{A}(x))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.full_domain_admit_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical Boolean characteristic readout has exactly the ADMIT kernel.

**Theorem 1.6 (ADMIT cannot increase agreement).**

$$\forall X, b, A, x, y, \operatorname{agrees}(\operatorname{bundleWithAtom}(b, \langle.admit, \operatorname{admitKernel}(A)\rangle), x, y) \Rightarrow \operatorname{agrees}(b, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.adding_admit_atom_cannot_increase_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair accepted by the extended bundle still satisfies every old atom.

**Theorem 1.7 (ADMIT is antitone off diagonal).**

$$\forall X, b, A, p, p \in \operatorname{offDiagonalPairs}(X) \Rightarrow \left(\operatorname{agrees}(\operatorname{bundleWithAtom}(b, \langle.admit, \operatorname{admitKernel}(A)\rangle), \operatorname{fst}(p), \operatorname{snd}(p)) \Rightarrow \operatorname{agrees}(b, \operatorname{fst}(p), \operatorname{snd}(p))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.admit_atom_preserves_offDiagonalPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every full-carrier off-diagonal pair, extended agreement implies old agreement.

**Theorem 1.8 (Certificates erase to object anchors).**

$$\forall X, a, \operatorname{relation}(\operatorname{anchorKernel}(a)) = \operatorname{Setoid.ker}(\lambda x, \operatorname{decide}(x = a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.certificate_anchor_erasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The anchor kernel retains only equality with the anchored object.

**Theorem 1.9 (Constant packed observers are universal).**

$$\forall X, axis, o, c, (\forall x, \operatorname{observe}(o, x) = c) \Rightarrow (\forall x, y, \operatorname{relation}(\operatorname{kernel}(\operatorname{toPrimitiveAtom}(axis, o)), x, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constant_packed_observer_has_universal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A proof-derived constant readout cannot distinguish carrier states.

**Theorem 1.10 (Universal atoms are neutral).**

$$\forall X, b, p, x, y, (\forall x, y, \operatorname{relation}(\operatorname{kernel}(p), x, y)) \Rightarrow (\operatorname{agrees}(\operatorname{bundleWithAtom}(b, p), x, y) \iff \operatorname{agrees}(b, x, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.universal_kernel_atom_does_not_change_agrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting a universally relating atom leaves bundle agreement unchanged.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.adding_admit_atom_cannot_increase_agreement`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.admit_atom_preserves_offDiagonalPairs`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.bundleWithAtom`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.certificate_anchor_erasure`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.closed_truth_readout_has_universal_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constantCutBundle`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constant_cut_bundle_has_universal_agreement`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.constant_packed_observer_has_universal_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.full_domain_admit_encoding`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.universal_kernel_atom_does_not_change_agrees`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/RoleSignature](RoleSignature.md)
