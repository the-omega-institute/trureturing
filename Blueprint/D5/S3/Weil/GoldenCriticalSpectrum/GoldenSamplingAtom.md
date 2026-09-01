# Golden Sampling Atom

## Abstract

Golden negative-time sampling gives damped complex atoms inside the unit disk, with the birth boundary exactly on the unit circle.

**Theorem 1.1 (Golden Sampling Locates Damped Modes in the Unit Disk).**

$$\forall gamma: \mathbb{R}, h: \mathbb{R},\\{}((\left\lVert \operatorname{goldenSamplingAtom}\left(gamma, h\right) \right\rVert = Real.goldenRatio^{-2 \times h}) \land (((\left\lVert \operatorname{goldenSamplingAtom}\left(gamma, h\right) \right\rVert = 1) \Leftrightarrow (h = 0)) \land ((0 < h) \Rightarrow (\left\lVert \operatorname{goldenSamplingAtom}\left(gamma, h\right) \right\rVert < 1)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_modulus_and_location` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sampled atom has exact radius phi raised to minus twice its height, independently of its phase frequency.

Its radius is one exactly at height zero, while every positive height gives strict unit-disk membership.

**Theorem 1.2 (Height One Gives a Strict Interior Atom).**

$$((\left\lVert \operatorname{goldenSamplingAtom}\left(0, 1\right) \right\rVert = Real.goldenRatio^{-2 \times 1}) \land (\left\lVert \operatorname{goldenSamplingAtom}\left(0, 1\right) \right\rVert < 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_inside_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At frequency zero and height one, the atom has exact radius phi to the power minus two.

The same calculation proves that this concrete radius is strictly less than one.

**Theorem 1.3 (Height Zero Refutes the Strict Interior Conclusion).**

$$((\left\lVert \operatorname{goldenSamplingAtom}\left(0, 0\right) \right\rVert = 1) \land (\neg \left\lVert \operatorname{goldenSamplingAtom}\left(0, 0\right) \right\rVert < 1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_boundary_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At frequency zero and height zero, the atom has norm exactly one.

This concrete boundary value violates the positive-height premise and makes the strict unit-disk conclusion false.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_boundary_counterexample`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_inside_witness`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.golden_sampling_atom_modulus_and_location`
- Dependency: [D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer](GoldenReflectionTransfer.md)
