# Rotation Orbit Gap Partition

## Abstract

Finite rotation orbit gaps partition the unit circle.

**Theorem 1.1 (Rotation orbit gaps partition the circle).**

$$0<n\Rightarrow g_{O_{\alpha,n}}(x)>0\ (x\in O_{\alpha,n}),\qquad \sum_{x\in O_{\alpha,n}}g_{O_{\alpha,n}}(x)=1.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/RotationOrbitGapsPartition.rotation_orbit_gaps_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fractional parts of the first n multiples of a real rotation parameter lie in the half-open unit interval. For positive n, the orbit contains its zeroth point, so the cyclic gap partition applies: every clockwise gap is positive and their sum is one. At parameter one half and length two, the orbit is exactly zero and one half; zero uses the ordinary successor while one half uses the wrap branch.
