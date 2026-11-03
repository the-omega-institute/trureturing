# Every natural 2<=a<c, d=c+1<b

## Abstract

Second peak, adjacent tail: complete physical joint lift

**Theorem 1.1 (One old permutation and its single literal fresh insertion).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Endpoint.actualSource_second_peak_adjacent_tail_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Endpoint.actualSource_second_peak_adjacent_tail_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural quadruple 2<=a<c, d=c+1<b, let k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There is one permutation sigma of all actual Fin k labels and one cut j<=k. Both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) hold. The same witnesses satisfy both strip bounds for every natural repetition count r and prefix length n, including zero and prefixes beyond the finite repeated list. Each repeated row separately has total zero.

With x=2^a,z=2^c,q=2^(b-c), the source heads and the paired residual windows are those in Algebra. The unbounded integer selector supplies v and m in the original V and W stocks. PhysicalBanks and PhysicalWord retain every source label, construct the same old word and insert the literal fresh label at cut d. The three exceptional triples use their explicit original words and cuts.

The PacketNormalForm actual-source equivalence supplies both complete OriginalOrder clauses from the physical strips. The existing zero-period transport applies separately to the old and new rows and preserves all natural takes and repetition counts. This result concerns the specified adjacent-tail sector; the entire Circle problem remains open. The ordinary construction is caller supplied, without a literature novelty claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Endpoint.actualSource_second_peak_adjacent_tail_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/BoundaryWords](BoundaryWords.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/PhysicalWord](PhysicalWord.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Rounding](Rounding.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
