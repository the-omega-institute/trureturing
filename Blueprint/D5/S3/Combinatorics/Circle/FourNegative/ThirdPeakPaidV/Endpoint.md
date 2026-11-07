# Original labels and exact unbounded domain

## Abstract

Paid low V with a shifted high allocation: original-source joint lift

**Theorem 1.1 (The full original six-hypothesis region).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Endpoint.actualSource_third_peak_paid_V_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Endpoint.actualSource_third_peak_paid_V_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original natural tuple 2<=a<b<=d<c, a+2<=d and c<=b+d-2, let k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exist a permutation sigma of all original Fin k labels and the exact freshCut j<k. OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) both hold.

The ear word inserts the sole fresh label k before the V terminal when Rp<0 and before the X terminal otherwise. The theorem retains the equality between j and the constructed cut, and uses the original seed and actualSource in both rows. Every natural finite repetition and every natural take have scalar sums in [0,modulus(k)/2] for the old row and [0,modulus(k)] for the new row. Each repeated row has total zero separately, including zero repetitions and takes beyond the finite word.

The proof lifts the exact physical word and uses the canonical original-source bridge and zero-period transport. It imports the private construction in the four companion modules. The construction was supplied in the caller's paid-V/W proof and authenticated five-module source draft, with independent ordinary mathematical approval. Those inputs are fallible; only current Lean elaboration and the scoped axiom report establish the typed result. Independent fixed-source review and official freezing remain separate.

The construction applies to the stated unbounded paid-V region, including b=d when the remaining inequalities hold. It does not close the entire third-peak cone, unrestricted Circle J, or C3.1. No literature novelty claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Endpoint.actualSource_third_peak_paid_V_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Allocation](Allocation.md)
