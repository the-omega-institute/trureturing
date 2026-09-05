# Peak-Lipschitz Zero-Free Disk

## Abstract

A strict peak-versus-displacement budget certifies a zero-free disk, and an affine function places a zero exactly at the limiting radius.

**Theorem 1.1 (Strict displacement budget excludes zeros).**

$$r> 0, L\geq 0, Lr< A,\quad \Vert f(w) \Vert\geq A,\quad \Vert f(z)-f(w) \Vert\leq L\operatorname{dist}(z, w)\quad \Rightarrow\quad \operatorname{dist}(z, w)< r\quad \Rightarrow\quad f(z)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PeakLipschitzZeroFreeDisk.strict_peak_lipschitz_zero_free_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive radius and nonnegative slope make Lr nonnegative, so the strict budget Lr < A also proves A is positive. The center norm is at least A, while every displacement in the radius-r disk changes the value by at most L times the distance. The strict budget Lr < A makes a zero impossible throughout the disk.

This is the formal core of the Bernstein and peak-height chain in source Theorem 6.180. The source's polynomial-specific Bernstein estimate and numerical Bragg data supply A and L; they are not silently assumed or reproduced by this abstract disk lemma.

Repository and pinned-Mathlib searches found nearby analytic-ball tools but no packaged strict peak-budget theorem.

**Theorem 1.2 (The limiting radius is sharp).**

$$A> 0, L> 0\quad \Rightarrow\quad f(z)=A-Lz,\quad \Vert f(0) \Vert=A,\quad f(\frac{A}{L})=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PeakLipschitzZeroFreeDisk.peak_lipschitz_radius_is_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For A,L > 0, the affine model f(z)=A-Lz has center norm A, exact Lipschitz slope L, and a zero at distance A/L. This constructive boundary witness shows why the zero-free conclusion uses a strict disk.

## References

- Truth anchor: `D5/S3/Zeros/PeakLipschitzZeroFreeDisk.peak_lipschitz_radius_is_sharp`
- Truth anchor: `D5/S3/Zeros/PeakLipschitzZeroFreeDisk.strict_peak_lipschitz_zero_free_disk`
