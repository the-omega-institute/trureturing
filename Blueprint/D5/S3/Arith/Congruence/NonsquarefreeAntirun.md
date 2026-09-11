# The sharp bound for nonsquarefree antiruns

## Abstract

Full intervals of nonsquarefree numbers with successive gaps greater than one have at most nine entries.

**Theorem 1.1 (Every nonsquarefree antirun has length at most nine).**

Lean statement: `D5/S3/Arith/Congruence/NonsquarefreeAntirun.antirun_length_le_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/NonsquarefreeAntirun.antirun_length_le_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2024). *OEIS A373409, Length of the n-th maximal antirun of nonsquarefree numbers differing by more than one*. URL: <https://oeis.org/A373409>.

*Commentary.*

FullNonsquarefreeInterval requires a strictly increasing list, nonsquarefreeness of every entry, and membership of every nonsquarefree number between any two entries. Thus the list occupies consecutive positions in the increasing enumeration. The antirun need not be maximal.

Multiples of four and nine force adjacent pairs at offsets 8 and 9, and at offsets 27 and 28, in every block of 36 integers. A full antirun cannot cross either pair. Ten entries separated by at least two need a span of at least 18. The only remaining interval has offsets 9 through 27, forcing the second entry to have offset 11. Fullness also requires the multiple of four at offset 12, contradicting the gap condition.

The private theorem nine_term_witness verifies the full interval 6345, 6348, 6350, 6352, 6354, 6356, 6358, 6360, 6363, including all intervening numbers and every gap. Its length is nine, so the bound is attained.

## References

- Truth anchor: `D5/S3/Arith/Congruence/NonsquarefreeAntirun.antirun_length_le_nine`
