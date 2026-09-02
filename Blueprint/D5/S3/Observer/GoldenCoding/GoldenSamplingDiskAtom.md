# Golden Sampling Disk Atom

## Abstract

Golden negative-time sampling sends positive-height modes inside the unit disk.

**Theorem 1.1 (Positive-height golden samples are disk atoms).**

$$\forall omega \in \mathbb{R}, hObserver \in \mathbb{R}, hMode \in \mathbb{R},\; hObserver < hMode \Rightarrow let h := hMode - hObserver; let q := \operatorname{goldenSamplingAtom}\left(omega, h\right); \left(\left(\left(q = \varphi^{{-2 \cdot h}} \cdot \operatorname{exp}\left(-i \cdot T_{\varphi} \cdot omega\right) \land \left\lVert q \right\rVert = \varphi^{{-2 \cdot h}}\right) \land \left\lVert q \right\rVert < 1\right) \land \left\lVert \operatorname{goldenSamplingAtom}\left(omega, 0\right) \right\rVert = 1\right) \land 1 < \left\lVert q^{-1} \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenSamplingDiskAtom.golden_sampling_disk_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The height h is the mode height minus the observer height, and T_phi is the repository's positive golden scale period. The displayed multiplier separates into a radial golden-ratio power and a unit-norm complex phase.

Strictly positive height makes the radial exponential less than one. The same norm calculation gives unit norm at height zero and places the reciprocal of every positive-height atom outside the unit disk.

The inverse-Fourier residue formula in the source depends on a transform convention not defined by the atom. This theorem records the self-contained pointwise consequence for its displayed multiplier.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenSamplingDiskAtom.golden_sampling_disk_atom`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix](../../CompletionDynamics/GoldenMobius/GoldenScaleHelix.md)
