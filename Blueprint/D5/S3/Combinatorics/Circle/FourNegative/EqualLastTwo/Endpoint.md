# The complete c=d boundary source family

## Abstract

Equal-last-two physical joint insertion

**Theorem 1.1 (All natural 2<=d<b<a, including both unbounded offset families).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Endpoint.actualSource_equal_last_two_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Endpoint.actualSource_equal_last_two_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,b,a with 2<=d<b<a, the implementation returns one permutation of all old physical labels, one literal cut, and the fresh ear insertion for the same physical order. The cut is 3d+1 when b=d+1 and a=d+2, and d in every other branch.

The branch b>=d+2 uses the 7/8 and 5/8 reserve banks. The adjacent strip b=d+1,a>=d+4 uses 15/16,13/16,5/16 and one low bank. The two offsets retain their exact labelled partitions and use exact doubled seam and peak polynomials in the unbounded dyadic parameter. Every positive local occurrence is retained exactly once, every negative occurrence is ordered explicitly, and both source totals are consumed.

The endpoint reconstructs every natural prefix from positive packet monotonicity, seam nonnegativity, peak bounds, the ear increment (0,A), and the final zero total. Overlong prefixes are included by the existing InStrip definition. No feasibility premise, rational certificate, cyclic covariance, or primitivity reduction is used.

The result covers exactly this complete boundary family. Unrestricted physical J and complete Circle C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Endpoint.actualSource_equal_last_two_joint_lift`
