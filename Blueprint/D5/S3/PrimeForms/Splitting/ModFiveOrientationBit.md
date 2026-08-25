# Modulo-Five Orientation Bit

## Abstract

The modulo-five orientation bit separates every binary three-ring profile fiber without defining a binary group character.

**Theorem 1.1 (The missing bit separates fibers but is not a group character).**

$$\begin{gathered}((\forall t: ThreeRingProfile, \Vert \{u: (\mathbb{Z}/60\mathbb{Z})^{\times} \mid triRingImage(u) = t\} \Vert = 2) \land\\{}(\forall t: ThreeRingProfile, u, v: (\mathbb{Z}/60\mathbb{Z})^{\times},\\{}triRingImage(u) = t \land triRingImage(v) = t \land\\{}\omega_{5}(u) = \omega_{5}(v) \Rightarrow u = v)) \land\\{}\neg(\forall u, v: (\mathbb{Z}/60\mathbb{Z})^{\times},\\{}\omega_{5}(u \times v) = \omega_{5}(u) + \omega_{5}(v)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/ModFiveOrientationBit.mod_five_orientation_separates_fibers_but_is_not_homomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit class u modulo sixty, modFiveOrientation(u) is zero when the residue of u modulo five is 1 or 2, and is one when that residue is 3 or 4.

Every three-ring profile fiber has exactly two unit classes. Equal orientation bits on two classes in the same fiber force those classes to be equal, so the bit distinguishes the two classes.

The contrast is structural: the bit does not send multiplication in the unit group to addition modulo two. Concretely, the class of seven has bit zero while its square, the class of forty-nine, has bit one.

Repository search supplied the exact two-element-fiber theorem and it is applied directly. Searches of the repository and pinned Mathlib found no theorem packaging the orientation test, its fiberwise separation, and the non-homomorphism contrast.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/ModFiveOrientationBit.mod_five_orientation_separates_fibers_but_is_not_homomorphic`
- Dependency: [D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers](ThreeRingProfileFibers.md)
