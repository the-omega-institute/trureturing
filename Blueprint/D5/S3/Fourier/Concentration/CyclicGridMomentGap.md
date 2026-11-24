# Phase separation and Fourier moment variance

## Abstract

The real projection variance controls separation from orthogonality.

Write m and b for a first and a second complex moment. Let c be the squared magnitude of m, s the product c(1−c), and D the real projection variance c/2−c²+Re(conjugate(m)² b)/2. Given the separation δ, let d be the maximum of δ−|2c−1| and zero.

**Theorem 1.1 (The variance bound for separated unit phases).**

$$0 < d \implies c \cdot d^{2} \leq 4 \cdot (1+\frac{4}{s}+\frac{c \cdot d^{2}}{s^{2}}) \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicGridMomentGap.phase_separation_variance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite indexed family of complex unit phases z and nonnegative real weights w that sum to one. Let m be the weighted sum of the phases and b the weighted sum of their squares. For each pair of indices with positive weight, assume the absolute real part of the product of one phase and the conjugate of the other is at least δ.

A diagonal pair bounds δ by one, so positive d implies c lies strictly between zero and one. Rotate and scale by the conjugate of m. The stability estimates `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability` control squared error to the two comparison phases and the difference of the sign-class masses. Averaging the squared perturbation of the real inner product over pairs from opposite classes gives ab c d² at most the total squared error, with a,b the class masses. Substitute four times their product as one minus the squared mass difference to get the claimed inequality.

**Theorem 1.2 (The variance bound on a cyclic grid).**

$$0 < d \implies c \cdot d^{2} \leq 4 \cdot (1+\frac{4}{s}+\frac{c \cdot d^{2}}{s^{2}}) \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicGridMomentGap.cyclic_grid_fourier_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a positive integer with four not dividing q and w a real probability weight on the residues. Let m and b be the coefficients at residues one and two of the unnormalized DFT with negative phase. Take δ=sin(pi/(2q)) for odd q and δ=sin(pi/q) for even q.

For an integer difference k of residues, center 4k−q modulo 2q. The centered integer has absolute value at least one for odd q and at least two for even q. Sine monotonicity gives the required bound on the absolute real product of the two character values. The phase variance theorem then gives the result with those moments. A positive-resolution bound at growing order for actual zeta ordinates remains open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicGridMomentGap.cyclic_grid_fourier_gap`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicGridMomentGap.phase_separation_variance_bound`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicMomentStability.first_two_moment_stability`
- Dependency: [D5/S3/Fourier/Concentration/CyclicMomentStability](CyclicMomentStability.md)
