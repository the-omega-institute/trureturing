# Absolute tails on the planar integer frequency lattice

## Abstract

Counting planar integer frequency shells gives an explicit Fourier tail bound.

**Theorem 1.1 (Tail bound for sixth-power decay).**

Lean statement: `D5/S3/Fourier/Asymptotics/PlanarFourierTail.lattice_fourier_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/PlanarFourierTail.lattice_fourier_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the radius of an integer frequency pair be the maximum of the absolute values of its two coordinates. Fix a positive integer cutoff J, a positive scale ε, and a nonnegative constant K. Consider any finite set of pairs of radius k greater than J. Suppose the complex coefficient at each selected pair has norm at most K ε²/(1+εk)⁶. Their norms sum to at most 2K/(ε⁴J⁴).

Extend the selected norms by zero. Mathlib's Int.card_box and Int.mem_box identify and count the 8k points on the square shell of radius k. Bounding the coefficient on that shell gives at most 8K/(ε⁴k⁵) in total. The difference of the consecutive inverse fourth powers at k−1 and k dominates 4/k⁵, so its sum telescopes.

For a scaled smooth test on a two-dimensional torus, the estimate controls the discarded modes once the coefficient decay has been established. Bounds on the retained modes and the geometric approximation to the readout sublevel region are additional inputs.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/PlanarFourierTail.lattice_fourier_tail`
