# CIRPT Primitive Bundles

## Abstract

Finite role-labelled primitive families compute one joint observational kernel.

**Definition 1.1 (Primitive atom).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveAtom`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveAtom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An atom pairs one CIRPT role label with a decidable kernel on the state space.

**Definition 1.2 (Primitive bundle).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveBundle`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveBundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bundle stores a finite decidable index type and one primitive atom per index.

**Definition 1.3 (Bundle agreement).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two states agree when every indexed atom kernel relates them.

**Definition 1.4 (Boolean bundle agreement).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agreesB`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agreesB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A commutative finite-set fold computes the executable Boolean conjunction.

**Definition 1.5 (Joint bundle kernel).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toKernel`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Logical agreement and its Boolean reflection are packaged as a decidable kernel.

**Definition 1.6 (Nonempty bundle).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.Nonempty`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.Nonempty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bundle nonemptiness is inhabitation of the packed index type.

**Definition 1.7 (Packed observer).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PackedObserver`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PackedObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A readout packages its codomain, decidable equality, and observation function.

**Definition 1.8 (Packed observer atom).**

Lean statement: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toPrimitiveAtom`

*Formalization.* `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toPrimitiveAtom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A packed readout becomes a CUT kernel while retaining the supplied role label.

**Theorem 1.9 (Boolean agreement reflects logical agreement).**

$$\forall b, x, y, \operatorname{agreesB}\left(b, x, y\right) = true \iff \operatorname{agrees}\left(b, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agreesB_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boolean conjunction over the finite universal set is true exactly when every atom relates the pair.

**Theorem 1.10 (Bundle agreement is an equivalence).**

$$\forall b: \operatorname{PrimitiveBundle}\left(X\right), \operatorname{Equivalence}\left(\operatorname{agrees}\left(b\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflexivity, symmetry, and transitivity are inherited coordinatewise from every atom kernel.

**Theorem 1.11 (Bundle joint-kernel law).**

$$\{(x,y) \mid \operatorname{agrees}\left(b, x, y\right)\} = \operatorname{bigcap}i \{(x,y) \mid \operatorname{relation}\left(\operatorname{kernel}\left(\operatorname{atom}\left(b, i\right)\right), x, y\right)\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.primitive_bundle_joint_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of agreeing pairs is exactly the indexed intersection of atom collision sets.

**Theorem 1.12 (Bundle agreement is the canonical quotient-CUT joint kernel).**

$$\forall x, y, \operatorname{agrees}\left(b, x, y\right) \iff (x,y) \in \operatorname{jointKernel}\left(\lambda i, \operatorname{quotientCut}\left(\operatorname{kernel}\left(\operatorname{atom}\left(b, i\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.bundle_agrees_iff_jointKernel_quotientCuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalizing each atom through its quotient CUT identifies bundle agreement with the repository jointKernel.

**Theorem 1.13 (Equal packaged relations give congruent bundle agreement).**

$$(\forall x, y, \operatorname{relation}\left(\operatorname{toKernel}\left(b\right), x, y\right) \iff \operatorname{relation}\left(\operatorname{toKernel}\left(c\right), x, y\right)) \Rightarrow ((\forall x, y, \operatorname{agrees}\left(b, x, y\right) \iff \operatorname{agrees}\left(c, x, y\right)) \land\\(\forall x, y, \operatorname{agreesB}\left(b, x, y\right) = \operatorname{agreesB}\left(c, x, y\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees_congr_of_kernel_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This bundle-level congruence preserves logical agreement and its Boolean computation; it is an input to the later engine-level invariance proof.

**Theorem 1.14 (Packed observer reflection).**

$$\forall axis, obs, x, y, \operatorname{relation}\left(\operatorname{kernel}\left(\operatorname{toPrimitiveAtom}\left(axis, obs\right)\right), x, y\right) \iff \operatorname{observe}\left(obs, x\right) = \operatorname{observe}\left(obs, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toPrimitiveAtom_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated atom kernel relates precisely the states with equal observed outputs.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.Nonempty`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PackedObserver`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveAtom`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.PrimitiveBundle`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agreesB`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agreesB_eq_true_iff`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees_congr_of_kernel_eq`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.agrees_equivalence`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.bundle_agrees_iff_jointKernel_quotientCuts`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.primitive_bundle_joint_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toKernel`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toPrimitiveAtom`
- Truth anchor: `D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.toPrimitiveAtom_relation_iff`
- Dependency: [D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm](QuotientCutNormalForm.md)
