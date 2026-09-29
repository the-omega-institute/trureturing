# Adjacent Words for Conditional Deletion

## Abstract

Adjacent-swap words and the first-orientation source shape.

Generators are numbered from one. A word is reduced when its length is minimal among all valid words for the same permutation. A singleton word is also consecutive: adjacent letters differ by one.

**Definition 1.1 (Adjacent swap).**

$$\operatorname {adj}\left(n, k\right) = \operatorname {swap}\left(k - 1, k\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

On Fin(n+1), generator k swaps one-based positions k and k+1. The definition is total; valid words restrict k to 1 through n.

**Definition 1.2 (Word product).**

$$\operatorname {prod}\left(n, w\right) = \prod _ {k \in w} \operatorname {adj}\left(n, k\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.wordProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The list product follows the word order and uses right-to-left permutation action.

**Definition 1.3 (Valid generators).**

$$\operatorname {Valid}\left(n, w\right) \iff \forall k \in w , 1 \le k \le n$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.validWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Every letter lies between one and n.

**Definition 1.4 (Reduced word).**

$$\operatorname {Reduced}\left(n, w\right) \iff \operatorname {Valid}\left(n, w\right) \land \forall v , \operatorname {SameValidProduct}\left(n, v, w\right) \implies \operatorname {length}\left(w\right) \le \operatorname {length}\left(v\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.reducedWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

SameValidProduct means that v is valid and has the same product as w. This is global minimality, with no finite search bound.

**Definition 1.5 (Consecutive letters).**

$$\operatorname {Consecutive}\left(w\right) \iff \forall \operatorname {neighbors}\left(a, b, w\right) , a + 1 = b \lor b + 1 = a$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.consecutive` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Every neighboring pair differs by one; empty and singleton lists qualify.

**Definition 1.6 (Oscillation predicate).**

$$\operatorname {Oscillation}\left(w\right) \iff \operatorname {WeakIncreasing}\left(\operatorname {SegmentLengths}\left(\operatorname {Spikes}\left(w\right)\right)\right) \lor \operatorname {WeakIncreasing}\left(\operatorname {reverse}\left(\operatorname {SegmentLengths}\left(\operatorname {Spikes}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.oscillation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Spikes keeps the first and last letters and, in their word order, the internal strict peaks and valleys. SegmentLengths takes the absolute difference of each successive pair of spikes. For consecutive words this is the paper's oscillation condition: the lengths are weakly increasing or weakly decreasing. The predicate also extends to arbitrary lists, including short words with no internal spike.

**Definition 1.7 (Singleton reduced word).**

$$\operatorname {Singleton}\left(n, sigma, w\right) \iff \operatorname {Reduced}\left(n, w\right) \land \operatorname {Consecutive}\left(w\right) \land \operatorname {prod}\left(n, w\right) = sigma$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.singletonWord` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

Singleton is the paper's one-element commutation-class condition expressed using reducedness and consecutive letters.

**Definition 1.8 (Full excursion).**

$$\operatorname {Full}\left(m, M, i, j\right) = \operatorname {concat}\left(\operatorname {desc}\left(j, m\right), \operatorname {asc}\left(m + 1, M\right), \operatorname {desc}\left(M - 1, i\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.fullExcursion` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The descending, ascending, descending blocks form the first-orientation excursion.

**Definition 1.9 (Deleted excursion).**

$$\operatorname {Deleted}\left(m, M, i\right) = \operatorname {concat}\left(\operatorname {desc}\left(i - 1, m\right), \operatorname {asc}\left(m + 1, M\right), \operatorname {desc}\left(M - 1, i\right)\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.deletedExcursion` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The first descending block begins at i-1 after deletion.

**Definition 1.10 (Deletion image).**

$$\operatorname {Image}\left(i, j, p, q\right) = \operatorname {concat}\left(p, \operatorname {desc}\left(j, i\right), q\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.imageWord` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

The target word retains the descending run from j to i.

**Definition 1.11 (First-orientation source shape).**

$$\operatorname {SourceShape}\left(m, M, i, j, a, p, q\right) \iff a = \operatorname {concat}\left(p, \operatorname {Full}\left(m, M, i, j\right), q\right) \land \operatorname {PrefixBounds}\left(m, j, p\right) \land \operatorname {SuffixBounds}\left(i, M, q\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.sourceShape` (`✓ std3`).

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

PrefixBounds requires m<k<j for every letter of p; SuffixBounds requires i<k<M for every letter of q. This is a separate premise of the converse.

**Definition 1.12 (Source permutation hypotheses).**

$$\operatorname {ExactSource}\left(n, m, M, i, j, sigma\right) \iff 1 \le m < i \le j < M \le n \land \operatorname {EndpointValues}\left(sigma\right) \land \operatorname {ExteriorFixed}\left(sigma\right) \land \operatorname {NonoscSourceExists}\left(sigma\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeAdjacentWords.exactSourceHypotheses` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

EndpointValues says sigma(M+1)=m, sigma(m)=j+1 and sigma(i)=M+1, with sigma(m) different from m and sigma(M+1) different from M+1. ExteriorFixed fixes positions below m and above M+1. NonoscSourceExists asserts a singleton reduced word a for sigma that fails the oscillation test of paper Definition 3.1. The test keeps the first and last letters and the internal strict peaks and valleys, in their word order. For successive entries s,t of this sequence, the segment length is the absolute difference |s-t|, represented on natural numbers by (s-t)+(t-s). A word is oscillating exactly when these lengths are monotone in the broad sense: weakly increasing or weakly decreasing. Thus the existential word a has a length sequence of neither kind. This word need not be the separately supplied shaped singleton a0; NonoscSourceExists does not assert SourceShape for a, and the conditional converse does not require a0 to be nonoscillating. The nonfixed endpoint clauses and NonoscSourceExists are contextual paper hypotheses unused by the two conditional proofs after the actual shaped singleton a0 is supplied; they do not establish SourceShape for that singleton.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.adjacent`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.consecutive`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.deletedExcursion`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.exactSourceHypotheses`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.fullExcursion`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.imageWord`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.oscillation`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.reducedWord`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.singletonWord`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.sourceShape`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.validWord`
- Truth anchor: `D5/S1/Words/Permutations/MamedeAdjacentWords.wordProduct`
