# Complete strip ordering from conservation and two large occurrences

## Abstract

A finite zero-sum integer row with at most one occurrence of each sign above half capacity admits a complete physical-label ordering in the capacity strip.

**Theorem 1.1 (One complete order of the original labels).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoLargeOrdering.exists_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoLargeOrdering.exists_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, weight function f:Fin(n) to the integers, finite list labels of Fin(n), and integer B, assume labels.Nodup, B>=0, sum(labels.map(f))=0, and |f(x)|<=B for every x in labels. Assume also that for any x,y in labels, B<2f(x) and B<2f(y) imply x=y, and B<-2f(x) and B<-2f(y) imply x=y. Then there exists a list word of Fin(n) with word.Perm(labels) and SourceWidth.InStrip(f,B,0,word). Thus every integer prefix sum, including the empty and complete prefixes and prefixes indexed beyond the word length, belongs to [0,B], by SourceWidth.inStrip_prefix. The permutation preserves every physical occurrence: labels may omit ambient Fin(n) positions, and word contains exactly those supplied labels once each. Distinct labels may have equal weights.

First retire the unique label p with 2f(p)>B, if it exists, and start the remaining construction at H=f(p). If it does not exist, start at H=0. In either case every remaining positive weight is at most half capacity. Maintain 0<=H<=B, H+sum(remaining weights)=0, the half-capacity bound on remaining positives, the original absolute bounds, and uniqueness of a negative occurrence above half capacity. Each recursive step deletes one actual label with List.erase; List.perm_cons_erase and the induction permutation certify completeness.

When a negative q fits, append it and retain the invariant. Otherwise choose any remaining positive p. If H+f(p)>B, its half-capacity bound implies 2H>B. Every negative q would then satisfy -f(q)>H and so -2f(q)>B. Conservation forces a negative to exist, and the uniqueness hypothesis makes all weights except that negative nonnegative. Their sum includes f(p), so conservation gives H+f(p)<=-f(q)<=B, a contradiction. This is the completion step: a positive fits whenever no negative fits. When no positive remains, SourceWidth.inStrip_nonpos consumes the entire remaining list using its conserved endpoint zero.

The theorem includes the empty list, all-zero rows, B=0, absence of either large occurrence, repeated values and arbitrarily many weights exactly at the half threshold. The threshold inequalities are strict doubled integer inequalities; no rounding convention is needed. The construction is existential and asserts a single complete order from zero. It does not assert that an arbitrary legal prefix extends. For B=10 the qualifying row (3,8,-6,-5) has a dead end after +3, whereas retiring +8 first permits completion.

The motivating circle source is the centered doubling orbit modulo an odd integer. On a least-period source with one cyclic positive run and one cyclic negative run, same-sign values form dyadic ladders, suggesting at most one above-half-capacity occurrence per sign at the maximum step magnitude. The formal obligations still to implement are extraction of those cyclic runs, derivation of the exact bounds and zero sum from the actual source, and label-preserving transport across rotation and repeated physical periods. The present theorem proves the general row construction only. Repeating a period can create multiple large occurrences in the full physical row; the intended application must apply this construction period by period and concatenate zero-total blocks.

Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671, asks for capacity C=(2^k-2)/2 for every positive k and every original source parameter. This general sufficient criterion neither discharges the cyclic two-run application nor settles that all-source conjecture. The full capacity-C conjecture remains open and active. No literature novelty, official uniqueness or model-diversity claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoLargeOrdering.exists_order`
- Dependency: [D5/S3/Combinatorics/Circle/SourceWidth](SourceWidth.md)
