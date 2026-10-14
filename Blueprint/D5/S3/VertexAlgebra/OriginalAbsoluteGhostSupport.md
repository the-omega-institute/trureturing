# Actual Native Ghost Support

## Abstract

Integral number degree separates the actual finite native kappa-zero branches.

**Theorem 1.1 (Finite Coefficient Support).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.native_ghost_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.native_ghost_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing nativeWord_J supplies the exact signed occupation eigenvalue. Applying the actual native coefficient map to the finite charge-sector expansion proves a diagonal coefficient equation. Integer cast injectivity and a nonzero actual coefficient force its degree to equal the degree of the original homogeneous state. This is a coefficient computation, not a spectral assumption on a transferred abstract equivalence.

**Theorem 1.2 (Degree One Eliminates The Up Branch).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.ghost_one_projector_relative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.ghost_one_projector_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual P coefficient diagonal forces kappa zero. The existing kappa_zero_iff then leaves exactly empty ghost support of degree one or singleton-three support of degree two. Homogeneity one eliminates the latter. Applying original B(0) to the full finite native expansion proves it vanishes, without assuming B(0) of the input state is zero.

**Theorem 1.3 (All Other Integral Degrees Vanish).**

Lean statement: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.projector_other_ghost_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.projector_other_ghost_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every supported coefficient of a P-fixed homogeneous charge-sector state has degree one or two. For every other integer degree the actual finite expansion is zero. No occupation cutoff or finite model replaces the original carrier. The reused eigenword and projector applications have no independent novelty credit.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.ghost_one_projector_relative`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.native_ghost_support`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport.projector_other_ghost_vanishes`
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/NativePhysicalRealization](RelativePairing/NativePhysicalRealization.md)
