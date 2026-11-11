# Physical internal transport and an integral local inverse

## Abstract

Physical internal transport and an integral local inverse.

**Theorem 1.1 (actual internal bits).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_bits`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r.

**Theorem 1.2 (actual internal readouts).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_readouts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r.

**Theorem 1.3 (selected internal step).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_internal_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_internal_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r.

**Theorem 1.4 (selected corrected ladders).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_corrected_ladders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_corrected_ladders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual upper-to-upper endpoint changes are read using the proved physical bit complements. An integral inverse eliminates the three local residuals; its Boolean coefficient relation is derived from the actual digits. Descending induction from the high base proves all corrected doubling ladders and zero triples, for every r.

Actual lower words of the differences. For 2<=j<=d-4, the three differences are R_(B/2+2^j)-R_(B/2), R_(B-b-2^j)-R_(B-b-2^(j+1)), and R_(B/2+a-2^j)-R_(B/2+a-2^(j+1)). Every endpoint is itself a selected UPPER row. All three physical words increase by 2^j. The lower j-bit signatures are (beta,0,1-alpha), (0,1-beta,1-sigma), and (sigma,alpha,0), for alpha=bit_j(a), beta=bit_j(b), sigma=bit_j(s).

Deriving the bit signatures. The proof uses divisibility by 2^(j+1) of the high powers. For a negative word -z, bit j complements bit j of z once a lower bit is nonzero. That condition is proved from a,b odd, and from s=2 mod 4 with j>=2. This is a uniform Euclidean-division argument on the actual words, not enumeration of r or a premise containing the claimed coefficient table.

The inverse coefficients. Let T=f+g+h, F=2f-f_next and G=2g-g_next. Under the already proved higher ladder and zero next triple, actual_internal_readouts derives rG=(2alpha-1)T+(1-alpha-beta)F+(1-alpha)G, rF=(2sigma-1)T+(1-sigma)F+(beta-sigma)G, and rH=T-sigma F-alpha G. Put e=alpha+sigma-2alpha sigma, tau=1-beta-e and omega=beta-e. The idempotent equations imply e^2=e and tau*omega=0. Thus L=rG-(2alpha-1)rH=tau F+G and M=rF-(2sigma-1)rH=F+omega G, giving F=M-omega L, G=L-tau M and T=rH+sigma F+alpha G.

A consumed inverse and descending induction. selected_internal_step applies this inverse to the actual vanishing corrected upper readouts, obtaining f_next=2f, g_next=2g, h_next=2h and T=0. selected_corrected_ladders descends from d-3 to 2 and proves Y_(p,j)=2^(j-2)Y_(p,2) and zero corrected triple at every j>=2. No determinant or supplied coefficient formula occurs in its presentation hypothesis.

Source-only boundary. The polynomial inverse and physical carry statements have source scripts, not kernel receipts. The ordinary eight-bit controls are not used as Lean proofs, and no rational-rank argument is used for saturation.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_bits`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.actual_internal_readouts`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_corrected_ladders`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows.selected_internal_step`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Binary](../MersenneExceptional19PermutationStabilizer/Binary.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows](../MersenneExceptional19PermutationStabilizer/CarryRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer](../MersenneExceptional19Stabilizer.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction](Correction.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows](HighRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout](Readout.md)
