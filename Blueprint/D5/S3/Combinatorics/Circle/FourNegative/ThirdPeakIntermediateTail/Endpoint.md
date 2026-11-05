# Every original 2<=a<=d<b<c

## Abstract

The full original intermediate-tail joint lift

**Theorem 1.1 (The original eight-binder source family).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Endpoint.actualSource_third_peak_intermediate_tail_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Endpoint.actualSource_third_peak_intermediate_tail_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original naturals a,b,c,d with 2<=a<=d<b<c, k is exactly a+b+c+d and the seed is exactly 1+2^a+2^(a+b)+2^(a+b+c). The public endpoint has exactly eight outer binders. It supplies an actual List(Fin k) permutation sigma and natural j=freshCut<k, the full old OriginalOrder, and the full enlarged OriginalOrder at twice the seed and the literal earWord(k,sigma,j). There is no selector, certificate, window premise or exponent upper bound.

The three physical constructions and four symbolic cases cover every original tuple. I uses s>=4 with W reserve h=3s/4-1 and p=h when r=1, p=sr/2-1 otherwise. II uses s=2,r>=2, W reserve r-1, and the adjacent V split. III uses s=2,r=1, the same V split, W reserve 1, and fresh at the start of bank1. The other cases insert at the start of bank2. Thus j=b in III and j=a+b+1 elsewhere. Negative terminal order is always V,W,X,U.

Native label, lift_order and marked_word reconstruct the actual original Fin labels and retain the literal insertion cut. The old modulus is modulus(k), the enlarged modulus modulus(k+1), and their repetition caps are respectively modulus(k)/2 and modulus(k). For all natural m,n the prefix of take n of m repetitions lies in the indicated closed interval, including zero repetitions, empty takes and takes beyond the repeated word. Every old repeated total and every new repeated total is independently zero, using native source_totals and zero_period_transport.

The dependent-family registration retains coordinates [0,1,2,3] and both actual OriginalOrder readouts. Its realization reconstructs the exact source proposition through the enrolled DependentFamily.realize template. Variation and role deletion change the full-family law. Actual observational dependence is witnessed separately at the admissible tuple (2,3,4,2): increasing lists satisfy the old and new orders at seed zero and fail at seed two. Each selected readout uses its actual natural seed operand.

The construction covers the complete unbounded intermediate-tail cone and retains the original labels, seed and insertion cut. No literature novelty is claimed. Unrestricted four-gap joint lifting and the full Circle/J/C3.1 remain OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Endpoint.actualSource_third_peak_intermediate_tail_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Physical](Physical.md)
