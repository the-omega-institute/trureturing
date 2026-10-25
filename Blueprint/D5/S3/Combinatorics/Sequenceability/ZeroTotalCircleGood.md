# Zero total connects circular arcs to actual Good intervals

## Abstract

Zero total connects circular arcs to actual Good intervals

**Theorem 1.1 (Zero total connects circular arcs to actual Good intervals).**

$$\forall G \in \mathrm{AddCommGroup},\; \forall A \in \mathrm{Finset}\left(G\right),\; \forall w \in \mathrm{List}\left(G\right),\; ((\mathrm{sum}\left(A\right) = 0) \land (w \in \mathrm{orders}\left(A\right))) \Rightarrow ((\mathrm{Good}\left(w\right)) \Leftrightarrow (\forall S \in \mathrm{Finset}\left(G\right),\; ((S \subseteq A) \land ((\mathrm{Nonempty}\left(S\right)) \land ((\mathrm{Nonempty}\left(\mathrm{sdiff}\left(A, S\right)\right)) \land (\mathrm{sum}\left(S\right) = 0)))) \Rightarrow (\neg \mathrm{Arc}\left(A, S, \mathrm{coeCycle}\left(w\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood.good_iff_no_zero_arc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

G ranges over additive commutative groups with decidable equality. Sum is coefficient-one original group addition. Good exempts exactly the full word, while Arc is an actual oriented circular run.

Good means that every nonempty proper contiguous interval of an actual original-group word has nonzero sum; only the full word is exempt. At total sum zero, the complement of every proper zero arc is another proper zero arc.

For any rooting of a circle split into two nonempty runs, at least one whole run remains a linear interval. Consequently a zero circular arc makes every rooting bad. Conversely a bad proper interval supplies its actual finite label set and its circular arc. This proves the exact bridge without weakening the interval convention.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/ZeroTotalCircleGood.good_iff_no_zero_arc`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularOrderCount](../CircularWords/CircularOrderCount.md)
- Dependency: [D5/S3/Combinatorics/Sequenceability/PairedZeroSubsetSpectrum](PairedZeroSubsetSpectrum.md)
