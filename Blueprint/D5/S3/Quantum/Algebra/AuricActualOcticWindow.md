# Actual characteristic-zero octic embedding frame

## Abstract

The repository's Auric octic source is realized over the fixed characteristic-zero field
`D = Q(2^(1/8))` with its original eight labels.  The source keeps the concrete positive
root, the primitive eighth root used for splitting, the finite extension carrying the
labels, and the exact transport of original quotients.  The full 43.2 support-fiber
classification and its cut-free matrix bridge remain open beyond this frame.

**Lemma 1.1 (The designated octic generator).** The positive real eighth root `aR` satisfies
`aR^8 = 2`; its complex image has minimal polynomial `X^8 - 2` over `Q`, and the canonical
intermediate field `D` is finite over `Q`.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricActualOcticWindow.aC_minpoly`,
`alpha_minpoly` and the finite-dimensional instance (`✓ scoped build pending cache recovery`). ∎

**Lemma 1.2 (Original labels and transport).** The adjoining field `K` contains the primitive
eighth root `zetaK`.  The maps `sigma i : D ->ₐ[Q] K` are the eight original labels,
are injectively indexed, and preserve multiplication, division, and nonzero denominators.
Their transported labels satisfy
`transported lambda i alpha = lambda aK * (lambda zetaK)^i` for every common coefficient
map `lambda`.

*Proof.* Machine-checked declarations are `sigma_label`, `sigma_zero`, `sigma_injective`,
`transported_label`, `transported_denominator`, and `transported_quotient` in the same
module; the current scoped build is pending the repository cache recovery. ∎

This frame deliberately does not claim the general 43.2 classification.  The missing
content is the actual trivial-multiplier argument: derive the strict intermediate projection
rank from the original idealizer condition, construct the square-zero rank-four operator,
prove the Galois-semilinear cut-free condition for every complementary label set, and
return the diagonal or transpose reconstruction to an original multiplier.  The source
premises and all eight labels remain fixed for that continuation.

## References

- Truth anchors: `D5/S3/Quantum/Algebra/AuricActualOcticWindow.aC_minpoly`,
  `D5/S3/Quantum/Algebra/AuricActualOcticWindow.alpha_minpoly`,
  `D5/S3/Quantum/Algebra/AuricActualOcticWindow.sigma_injective`
- Existing determinant input: `D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible`
- Source: `docs/develop/theory/AURIC_R5_023_CHARACTERISTIC_ZERO_HALF_WINDOW_RECOVERY.md`, §§26.9–26.16, 43.1–43.21
