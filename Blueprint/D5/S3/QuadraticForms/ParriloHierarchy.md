# The full copositive polynomial SOS hierarchy

## Abstract

The full copositive polynomial SOS hierarchy

For every level k, K consists of real symmetric M for which (sum_i X_i squared)^k times sum_ij M_ij X_i squared X_j squared is a native real sum of squares. The definitions use the genuine squared-variable substitution and cover every finite dimension, with no normalization. This is the hierarchy used by Gulati-Nechita-Park, not a substitution by the zeroth conic GDNN approximation. Its actual tensor-extension characterization remains a separate obligation.

**Definition 1.1 (Homogeneous form before squaring variables).**

Lean statement: `D5/S3/QuadraticForms/ParriloHierarchy.liftedForm`

*Formalization.* `D5/S3/QuadraticForms/ParriloHierarchy.liftedForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree is k+2. All ordered matrix entries contribute, so off-diagonal entries occur twice for symmetric matrices.

**Definition 1.2 (Actual Parrilo polynomial).**

Lean statement: `D5/S3/QuadraticForms/ParriloHierarchy.polynomial`

*Formalization.* `D5/S3/QuadraticForms/ParriloHierarchy.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native expand map substitutes X_i squared in the homogeneous form, yielding exactly the standard level-k polynomial.

**Definition 1.3 (Full native SOS hierarchy).**

Lean statement: `D5/S3/QuadraticForms/ParriloHierarchy.K`

*Formalization.* `D5/S3/QuadraticForms/ParriloHierarchy.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate is real symmetry and unrestricted native IsSumSq of the actual polynomial. Zero and singular matrices are retained.

**Theorem 1.4 (Increasing hierarchy).**

Lean statement: `D5/S3/QuadraticForms/ParriloHierarchy.hierarchy_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ParriloHierarchy.hierarchy_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by the genuine sum of squares sum_i X_i squared carries level k into level k+1.

**Theorem 1.5 (Closedness at every level).**

Lean statement: `D5/S3/QuadraticForms/ParriloHierarchy.K_closed`

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ParriloHierarchy.K_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real linear coefficient map of the degree-2(k+2) polynomial pulls back the closed native homogeneous SOS cone. Intersecting with real symmetric matrices proves closedness of every actual level.

## References

- Truth anchor: `D5/S3/QuadraticForms/ParriloHierarchy.K`
- Truth anchor: `D5/S3/QuadraticForms/ParriloHierarchy.K_closed`
- Truth anchor: `D5/S3/QuadraticForms/ParriloHierarchy.hierarchy_monotone`
- Truth anchor: `D5/S3/QuadraticForms/ParriloHierarchy.liftedForm`
- Truth anchor: `D5/S3/QuadraticForms/ParriloHierarchy.polynomial`
- Dependency: [D5/S3/QuadraticForms/HomogeneousSOSGram](HomogeneousSOSGram.md)
