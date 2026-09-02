# Delone Model-Set Certificates

## Abstract

Explicit separation and covering certificates promote a cut-and-project model set to Mathlib's bundled DeloneSet.

**Theorem 1.1 (Metric certificates are equivalent to a Delone structure on the model-set carrier).**

$$\operatorname{Nonempty}(\operatorname{Certificate}(S, W)) \iff \exists D, \operatorname{carrier}(D) = \operatorname{modelSet}(S, W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/DeloneModelSetCertificate.certificate_nonempty_iff_deloneSet_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate stores a positive packing radius with separation and a positive covering radius with a cover of the full physical space.

These fields are exactly the data expected by Mathlib's canonical Delone.DeloneSet structure.

The equivalence keeps the topological burden explicit. A bounded internal window alone does not manufacture a Delone theorem; specialized model sets must supply the two metric witnesses.

## References

- Truth anchor: `D5/S3/Fourier/DeloneModelSetCertificate.certificate_nonempty_iff_deloneSet_exists`
- Dependency: [D5/S3/Fourier/CutProjectScheme](CutProjectScheme.md)
