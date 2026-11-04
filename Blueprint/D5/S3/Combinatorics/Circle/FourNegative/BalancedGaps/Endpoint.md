# A complete chamber of physical J

## Abstract

Balanced four-independent-gap physical joint lift

**Theorem 1.1 (One physical permutation and one literal ear cut).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint.actualSource_balanced_gaps_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint.actualSource_balanced_gaps_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every independent a,b,c,d>=2 with max(a,b,c,d)<=min(a,b,c,d)+1, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exist one permutation sigma of the actual old physical labels Fin(k) and one cut<=k satisfying OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,cut)). This retains every natural take-prefix, both exact zero totals, the minimum s=2 boundary, all ties, nonprimitive seeds and repeated numerical values.

Write each gap as s or s+1 and q=2^s>=4. The sixteen fixed plans use negative-chain orders 0123,0123,1023,1302,2103,0321,0123,0123,3012,0231,3012,3210,3120,1230,1230,0123 and respective ear positions 0,3,2,1,2,1,2,3,2,2,1,0,1,2,3,0. Native positive packets are the actual chain intervals. Only in patterns 0110,1011,1101 is a single local-exponent-zero occurrence transferred, respectively 2->0,0->2,0->1. Every old occurrence is retained exactly once. The ear is placed after its packet positives immediately before the selected negative.

The accepted physical source identities and geometric sums determine all masses. After doubling, all 256 seam and peak-slack polynomials have nonnegative coefficients in q-4, proved by ordinary kernel-checked ring normalization and ordered-ring nonnegativity. The physical certificate equivalence turns the endpoint inequalities into full prefix strips and a literal cut. Internal increments are positive in both rows; the ear is nonnegative in the old/new pair. The old and new totals come from the actual source identities.

This closes the entire balanced chamber of the four-independent-gap problem. Unrestricted physical J remains OPEN. Source C4 rotation is not asserted to preserve joint witnesses; these finite S4 order choices and occurrence transfers are explicit proof data. No novelty claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint.actualSource_balanced_gaps_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Certificate](Certificate.md)
