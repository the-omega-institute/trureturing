# Binary Geometric Baseline

## Abstract

The binary geometric baseline has order one, a one-dimensional solution space, one characteristic root, and fingerprint one.

**Theorem 1.1 (The binary geometric recurrence is first order).**

$$\operatorname{order}\left(\mathit{Rbinary}\right) = 1 \land \operatorname{IsSolution}\left(\mathit{Rbinary}, \left(2^{n}\right)_{n \in N}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/BinaryBaseline.binary_geometric_recurrence_first_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence has order one, and the geometric sequence with nth term two to the n is a solution. Thus each next term depends only on the immediately preceding term.

**Theorem 1.2 (The binary recurrence solution space is one-dimensional).**

$$\operatorname{dim}\left(C, \operatorname{Sol}\left(\mathit{Rbinary}\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/BinaryBaseline.binary_recurrence_solution_space_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard initial-value basis identifies the solution space with one complex initial coordinate, so its finite dimension is one.

**Theorem 1.3 (The binary characteristic polynomial has exactly one root).**

$$\operatorname{roots}\left(\operatorname{charPoly}\left(\mathit{Rbinary}\right)\right) = \left\{2\right\}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/BinaryBaseline.binary_characteristic_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characteristic polynomial is X minus two, and its root multiset is the singleton containing two. This is the formal no-hidden-face assertion.

**Theorem 1.4 (Binary baseline package).**

$$\left(\operatorname{order}\left(\mathit{Rbinary}\right) = 1 \land \operatorname{IsSolution}\left(\mathit{Rbinary}, \left(2^{n}\right)_{n \in N}\right)\right) \land \left(\operatorname{dim}\left(C, \operatorname{Sol}\left(\mathit{Rbinary}\right)\right) = 1 \land \left(\operatorname{roots}\left(\operatorname{charPoly}\left(\mathit{Rbinary}\right)\right) = \left\{2\right\} \land \mathit{binaryCodingFingerprint} = 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/BinaryBaseline.binary_baseline_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order-one recurrence, one-dimensional solution space, and singleton characteristic root are conjoined with the frozen binary coding fingerprint value one.

The singleton root is the precise no-hidden-face content. The source phrase collapse back to zeta itself is not formalized: the imported S0 interfaces provide no corresponding zeta-layer object or two-sided construction, so no zeta claim appears in this package.

## References

- Truth anchor: `D5/S0/Tower/Champions/BinaryBaseline.binary_baseline_package`
- Truth anchor: `D5/S0/Tower/Champions/BinaryBaseline.binary_characteristic_roots`
- Truth anchor: `D5/S0/Tower/Champions/BinaryBaseline.binary_geometric_recurrence_first_order`
- Truth anchor: `D5/S0/Tower/Champions/BinaryBaseline.binary_recurrence_solution_space_finrank`
- Dependency: [D5/S0/Tower/Champions/CodingFingerprint](CodingFingerprint.md)
