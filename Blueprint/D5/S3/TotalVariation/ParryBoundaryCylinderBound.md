# Boundary selection from actual run cylinders

## Abstract

Finite run cylinders control both boundary selections under the stationary Parry law.

**Theorem 1.1 (Two finite-family bounds).**

Lean statement: `D5/S3/TotalVariation/ParryBoundaryCylinderBound.parry_boundary_cylinder_bound`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryBoundaryCylinderBound.parry_boundary_cylinder_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a forbidden one-run length k at least two, a window length R, and a positive run count n. Let C be any finite set of lists of n pairs (z,w), with z at least one and w between one and k minus one. For each list, two plus the sum of z+w must be at most R. Write p for the actual Parry parameter. Let S be the sum over C of p raised to that total span. Let M be the same sum restricted to lists whose first zero-run length is at least every zero-run length.

Apply the original longest complete zero-run selector to the R observed relation bits of the stationary signed state path. The mass of paths for which the selected opening endpoint is zero is at most the stationary mass of the word 10 times 1-S+M. The mass of paths for which the selected closing endpoint is R minus one is at most the stationary mass of 01 times the same factor. Both events use the identical selector, including its preference for the latest closing endpoint on ties. The sums range over actual finite state prefixes with the reference law and Parry initial law.

A code starts with 10 and continues through the prescribed zero and one runs, ending at the first zero of the next run. Its word length is two plus the total span. A pair (z,w) describes a positive gap z followed by w minus one zero gaps between successive ones. The exact gap geometry identifies every prescribed positive gap with a complete candidate. Its two boundary ones remain visible under every continuation of the window. The final zero is an incomplete tail and creates no additional prescribed candidate.

Exact parsing makes distinct codes with n runs incompatible as prefixes of one word. Reversing the words gives the corresponding disjoint suffix cylinders. Summing all finite continuations uses transition row normalization on the right and stationarity on the left. The complete-run laws then give each cylinder mass as its boundary mass times p raised to the total span.

If a boundary candidate is selected inside a code cylinder, its zero run is the first encoded run and cannot be shorter than any encoded competitor. For the closing boundary, reversal sends an interval (a,b) to (R-1-b,R-1-a), preserving its zero-run length. Thus only cylinders counted by M can intersect the selected-boundary event. Outside the disjoint cylinders the remaining boundary mass is at most the stationary two-bit boundary mass times 1-S. Adding these two contributions proves both estimates without conditioning on fit or dividing by S.

The finite family may be empty, and R may be zero. No renewal independence premise is needed. These estimates do not assert the scalar shared-rule defect bound of 512 divided by R.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryBoundaryCylinderBound.parry_boundary_cylinder_bound`
- Dependency: [D5/S3/TotalVariation/ParryRunPrefixCode](ParryRunPrefixCode.md)
