# Sampling smooth planar windows

## Abstract

Fourier mode estimates control weighted sampling of small periodic windows.

**Definition 1.1 (Planar torus character).**

Lean statement: `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.character`

*Formalization.* `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.character` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an integer frequency m and a planar representative p, the character is exp(2πi⟨p,m⟩). The factor 2π fixes the period of each coordinate to one.

**Theorem 1.2 (Uniform error for a rescaled smooth window).**

Lean statement: `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.compact_window_sampling`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.compact_window_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a smooth compactly supported complex function f on the Euclidean plane. There is a nonnegative constant K depending on f. For 0 < ε ≤ 1 and any center, scale f by ε and sum its integer translates. Take any finite sample of planar representatives with nonnegative real weights totaling one. For a positive integer J and nonnegative reals c and d, suppose that each nonzero mode of radius k ≤ J has weighted character average of norm at most c + dk². The radius is the maximum of the two absolute coordinates.

The norm of the difference between the weighted average of the periodized window and ε² times the plane integral of f is at most 27Kc + 27Kd/ε² + 2K/(ε⁴J⁴).

The change of variables gives an ε² factor in each Fourier coefficient. Schwartz decay bounds the remaining factor by a constant times (1+εk)⁻⁸, uniformly over the center. Compact support makes the integer translates locally finite, so coordinate Poisson summation identifies the periodization with its absolutely convergent series. An enclosing lattice square and the sixth-power tail bound control the absolute coefficient sum and its second moment. Unit-modulus characters and the normalization of the weights bound the discarded-mode averages by one.

For a sample of zero ordinates, the bounds on the retained modes are arithmetic inputs. Counts for an indicator window also require upper and lower approximations of that indicator.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.character`
- Truth anchor: `D5/S3/Fourier/Asymptotics/PlanarWindowSampling.compact_window_sampling`
- Dependency: [D5/S3/Fourier/Asymptotics/PlanarFourierTail](PlanarFourierTail.md)
- Dependency: [D5/S3/Fourier/CoordinatePoisson](../CoordinatePoisson.md)
