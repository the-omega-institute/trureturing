# FishburnTenSevenWords

## Abstract

Two languages over three letters encode block restrictions and are related by reversal and interchange.

**Definition 1.1 (Three allocation letters).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Letter`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Letter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

The alphabet consists of the three letters d, i and j.

**Definition 1.2 (Order between occurrences of two letters).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Before`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Before` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

For letters earlier and later, the order condition requires that no occurrence of later precede an occurrence of earlier at a strictly larger position in the word.

**Definition 1.3 (The first word language).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageA`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Language A of size consists of words of that length over d, i and j having no adjacent j followed by i and no d before a later j.

**Definition 1.4 (The third word language).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageC`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

Language C of size consists of words of that length over d, i and j having no adjacent j followed by i and no i before a later d.

**Definition 1.5 (Interchanging two letters).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.swap`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.swap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

The interchange fixes d and exchanges i and j.

**Definition 1.6 (Reversal and interchange).**

Lean statement: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.phi`

*Formalization.* `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Eric S. Egge (2022). *Pattern-Avoiding Fishburn Permutations and Ascent Sequences*. DOI: [10.48550/arXiv.2208.01484](https://doi.org/10.48550/arXiv.2208.01484). URL: <https://arxiv.org/abs/2208.01484v1>.

*Commentary.*

The word transformation interchanges i and j at every position, fixes d, and reverses the resulting word.

## References

- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Before`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.Letter`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageA`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.languageC`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.phi`
- Truth anchor: `D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.swap`
