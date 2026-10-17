# Smooth Approximation in the Same Window

## Abstract

Smooth an interior box without enlarging the original window, then control the error by the width of its two boundary strips.

**Definition 1.1 (An interior smooth box).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowCutoff`

*Formalization.* `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let h be positive and let a be at least 4h. Average the box of radius a-3h/2 against the existing normalized even smooth seed of radius h/2. Multiplication by the box length removes its normalization. The result is an even smooth compactly supported complex function.

**Definition 1.2 (An actual smooth test).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial`

*Formalization.* `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the interior cutoff by any even infinitely differentiable complex function p. No compact-support hypothesis on p is needed: the cutoff supplies compactness. In particular, this construction applies to every finite even cosine polynomial.

**Theorem 1.3 (Support, plateau and variation).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The smooth test is supported in [-a+h,a-h] and agrees with p on [-a+2h,a-2h]. On this central interval, every translate of the seed support lies inside the averaging box, so the integral equals the seed's full unit mass. The complementary cutoff has norm at most one by integrating over the complementary set. The existing box-average derivative estimate gives a cutoff derivative L1 norm at most two, independently of h.

**Theorem 1.4 (An explicit boundary-layer error).**

Lean statement: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_L1_error_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_L1_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the norm of p is at most a nonnegative M on [-a,a]. Compare the smooth test with the zero extension of p from the open interval (-a,a). The error vanishes on the central plateau and outside the original window. On each remaining boundary strip its norm is at most M. The two strips have total length 4h, giving L1 error at most 4Mh. This unweighted estimate alone does not establish convergence in a logarithmically weighted Fourier norm or in the Weil quadratic-form norm.

## References

- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowCutoff`
- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial`
- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_L1_error_le`
- Truth anchor: `D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.sameWindowSmoothTrial_budget`
- Dependency: [D5/S3/Weil/BurnolGram/FiniteBoxWeilMollifier](FiniteBoxWeilMollifier.md)
