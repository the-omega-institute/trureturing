# Three-Ring Profile Fibers

## Abstract

The Gaussian, Eisenstein, and golden readings on units modulo sixty realize every split-inert profile exactly twice.

**Theorem 1.1 (Every three-ring profile has exactly two unit classes).**

$$\operatorname{Surjective}\left(triRingImage\right) \land\\\forall t: ThreeRingProfile, \Vert \{u: (\mathbb{Z}/60\mathbb{Z})^{\times} \mid \operatorname{triRingImage}\left(u\right) = t\} \Vert = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers.tri_ring_image_surjective_with_fibers_of_card_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a unit class modulo sixty, the Gaussian coordinate records whether its residue is 1 modulo 4, the Eisenstein coordinate records whether it is 1 modulo 3, and the golden coordinate records whether it is 1 or 4 modulo 5.

These three readings jointly attain every combination of split and inert coordinates. Moreover, each profile is attained by exactly two unit classes, so the unit classes are partitioned into uniform two-element fibers over the eight possible profiles.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/ThreeRingProfileFibers.tri_ring_image_surjective_with_fibers_of_card_two`
