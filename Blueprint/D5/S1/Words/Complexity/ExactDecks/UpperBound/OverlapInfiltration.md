# OverlapInfiltration

## Abstract

Overlap infiltrations encode products of actual scattered counts with multiplicity.

The infiltration product and its top-degree shuffle stratum are classical and are also used in the cited source. The list-valued definitions retain one entry per alignment, so coincident output words remain repeated. The final unconditional recovery theorem is the repository bridge used by the exact asymptotic upper injection.

**Definition 1.1 (Overlap infiltrations with multiplicity).**

$$overlapInfiltrations$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.overlapInfiltrations` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For words left,right over a decidable alphabet, overlapInfiltrations recursively records a left-only, right-only, and, when the leading letters agree, shared-position branch. It is a list, so distinct alignments yielding the same merged word remain distinct entries.

**Definition 1.2 (Ordinary shuffles with multiplicity).**

$$ordinaryShuffles$$

*Formalization.* `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.ordinaryShuffles` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

ordinaryShuffles recursively interleaves the two words using the left-only and right-only branches, retaining one list entry per positional choice.

**Theorem 1.3 (The actual infiltration product identity).**

$$scatteredCountmuleqsumoverlapInfiltrations$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.scatteredCount_mul_eq_sum_overlapInfiltrations` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For all left,right,source over a decidable alphabet, scatteredCount left source times scatteredCount right source equals the sum of scatteredCount merged source over the full overlapInfiltrations list, including repeated merged words.

**Theorem 1.4 (The top-length stratum is shuffle).**

$$overlapInfiltrationsfiltertoplength$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.overlapInfiltrations_filter_top_length` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Filtering overlapInfiltrations left right to merged words of length left.length+right.length gives literal list equality with ordinaryShuffles left right, preserving every multiplicity.

## References

- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.ordinaryShuffles`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.overlapInfiltrations`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.overlapInfiltrations_filter_top_length`
- Truth anchor: `D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration.scatteredCount_mul_eq_sum_overlapInfiltrations`
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](../../VivionBinomialConverseFails.md)
