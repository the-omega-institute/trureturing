# Law Identification from Two Overlapping Paired Deletions

## Abstract

Two paired deletion channels taken from the same original cycle determine its full law when they overlap in one deleted label. A single paired channel can have a two-element fibre, caused by an adjacent swap, but the second channel turns that swap into a singleton at one endpoint.

Fix a finite support `A` with `4 ≤ A.card` and distinct supported labels `a`, `b`, and `c`. For a legal oriented cycle `C`, write

\[
F(C)=(D_a(C),D_b(C)),\qquad G(C)=(D_b(C),D_c(C)).
\]

The carrier identifies rotations and keeps reversal distinct. The two outputs in each pair come from the same source cycle.

**Theorem 1.1 (Signed law identification on every finite legal realization).**

For any finite type `ι` indexing an injective family of legal fixed-support cycles, if two real signed weights have equal pushforwards through `F` and equal pushforwards through `G`, then the weights are equal. The source declaration is `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.signed_injective`.

**Theorem 1.2 (Full fixed-support signed law identification).**

On the complete finite carrier

\[
\mathrm{FixedCycles}(A)=\{C : \mathrm{Cycle}(\alpha)\mid C.\mathrm{Nodup}\land C.\mathrm{toFinset}=A\},
\]

the two pushforwards `F_*` and `G_*` jointly are injective on real signed laws. This is `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.full_signed_injective`.

**Theorem 1.3 (Probability-law specialization).**

The same conclusion holds for probability laws on the complete carrier. The nonnegativity and total-mass hypotheses are recorded explicitly in `full_probability_injective`; the proof reduces to the signed statement.

*Proof idea.* R1 gives the exact fibre classification for one paired channel: a non-singleton fibre consists of a source cycle and the cycle obtained by swapping an adjacent `a,b` block. Choose a fourth support label outside `{a,b,c}` as a common cut. If a source and its `a,b` swap were both nontrivial in the overlapping `b,c` channel, the swap would have to move both `b` and `c` in the same rooted cycle, which is impossible. Thus every non-singleton `F`-fibre has a leaf for `G`, and every non-singleton `G`-fibre has the corresponding leaf for `F`. The singleton equations force the leaf weight to vanish; the two-element fibre equation then forces the remaining weight to vanish.

The proof uses the actual circular deletion geometry, including the wrap-around cut and the support-size-four boundary. It does not assume an abstract acyclic graph, a reversal quotient, or three independent marginal observations.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.signed_injective`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.full_signed_injective`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.full_probability_injective`
- Fibre geometry: [D5/S3/Combinatorics/CircularWords/PairedDeletionFiber](PairedDeletionFiber.md)
- Reconstruction boundary: [D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions](ThreeSpecifiedDeletions.md)
