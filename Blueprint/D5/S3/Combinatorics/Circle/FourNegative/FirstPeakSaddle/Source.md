# Four original chains and their enlarged counterparts

## Abstract

Literal source recurrences and centered bounds

**Lemma 1.1 (Eight exact recurrences).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_recurrences`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_recurrences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four source chain lengths are d,c,b,a. With N=xyzt-1 and Q=2N+1, the recurrences are tA=N+B, zB=N+L, yL=N+M, xM=N+A and t(2A)=Q+Bn, zBn=Q+Ln, yLn=Q+Mn, xMn=Q+A. The proof checks each native Fin4 index by ring normalization using the existing PacketNormalForm.Source constants.

**Lemma 1.2 (Odd bases and successors).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a,b,c,d>=2, the old modulus and old bases are odd, as are all enlarged successors. The enlarged first base 2A is even; no assertion that every enlarged base is odd is made.

**Lemma 1.3 (Bounds for exact ladder reduction).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_centered_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_centered_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old and enlarged bases lie from 1 to their respective modulus minus two. The proof reuses chain_values and new_base_bounds and combines parity with nonnegative charge. Physical uses these bounds and the recurrences to control the actual centered residues; no second source realization is assumed.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_centered_bounds`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_parity`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_recurrences`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint](../Descending/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure](Structure.md)
