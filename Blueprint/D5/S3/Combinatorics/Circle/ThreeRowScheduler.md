# Attained masks on all physical row labels

## Abstract

A source-specific attained mask retires the remaining large pair while preserving every physical occurrence.

small_batch orders distinct occurrence labels from any legal height h when every step has magnitude at most S, 0<=S, 2S<=B, and the final height h+sum(labels) also lies in [0,B]. Its endpoint need not be zero. The mask invocation in schedule_rows uses this stronger conclusion from F to W2+fgate, before the remaining tail returns to zero.

segment and physicalRows describe intervals of original Fin(3L+J+4) labels. physical_cover joins the intervals and all seven singled-out occurrences into the exact finRange list, splitting the old positive ladder into lower bits and its actual top bit. Equal source values remain distinct labels; no quotient by value or least-period assumption enters the cover.

schedule_rows starts with the row values and four physical dyadic lists, the complete-label permutation and integer total zero. dyadic_select partitions oldNeg with coefficient n-r and nextNeg with coefficient r-1. The selected negative labels attain R after M and -D; the first parent and terminal attain F. The unused mask consists of the old positive top label and the third negative ladder.

The arithmetic gate proves that scheduling this SMALL mask ends at W2+fgate. Executing terminal2 and parent2 then reaches V2+fgate within [0,C]. The untouched complement is aRest, zRest and oldPosLower; its signed sum is computed from the dyadic partitions, and the original total forces its final height to zero. A second small_batch invocation completes it. Permutation and Nodup arguments account for all labels at every stage.

The local actual_total adapter only converts the Finset sum supplied by ZeroSumSubsets.source_cycle to a finRange sum; the coboundary proof remains at that original owner. The sign bound on negative dyadic labels directly uses SourceWidth.dyadic_nonneg. The separate ThreeRowSource module reuses ThreeParentFamily.dyadic_ofFn to identify the four physical ladders and consumes this scheduler in its exact source construction.

The scheduler applies to the explicit unbounded three-row family. The final physical repetition and inverse cyclic relabeling are in ThreeRowSource. Universal j0 and full C3.1 remain open.

## References

- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
- Dependency: [D5/S3/Combinatorics/Circle/ThreeRowParameters](ThreeRowParameters.md)
- Dependency: [D5/S3/Combinatorics/Circle/ZeroSumSubsets](ZeroSumSubsets.md)
