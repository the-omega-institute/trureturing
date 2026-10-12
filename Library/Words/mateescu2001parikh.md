---
bibkey: mateescu2001parikh
authors: Alexandru Mateescu; Arto Salomaa; Kai Salomaa; Sheng Yu
year: 2001
title: A sharpening of the Parikh mapping
doi: 10.1051/ita:2001131
url: https://www.numdam.org/item/ITA_2001__35_6_551_0/
claim: "Definition 1.1 and Theorem 2.1 define the ordered Parikh matrix product and identify its upper entries with scattered-subword counts."
strata_touched:
  - D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge
license: citation-only
triage: anchor
---

# A sharpening of the Parikh mapping

Mateescu, A. Salomaa, K. Salomaa and Yu, RAIRO - Theoretical Informatics and
Applications 35(6), 551-564, define the Parikh matrix mapping for an ordered
alphabet. Definition 1.1 assigns to its j-th letter the identity matrix with
one additional entry at (j,j+1), and extends this assignment multiplicatively
in word order. Theorem 2.1 identifies the entry (i,j+1) with the number of
scattered occurrences of the consecutive alphabet segment from i through j.
The diagonal entries are one and the lower entries are zero.

For the binary specialization, the first letter is true and the second is
false. Converting the paper's one-based matrix indices to zero-based indices
gives the generators I+E01 and I+E12. The entries (0,1), (1,2) and (0,2) are
respectively the true count, false count and scattered true-before-false count.
The empty word maps to the identity. Casting these natural counts into the
integers does not change the attributed identity.

This note attests the standard product and its entry theorem. The connections
to the repository's factorial Chen signature, doubled Magnus center and
count-and-center recovery interface are separate repository derivations.
Recursive counting and matrix normalization helpers carry no novelty claim.

## Verified locator

- DOI: https://doi.org/10.1051/ita:2001131
- Archive record: https://www.numdam.org/item/ITA_2001__35_6_551_0/
- Original article: https://www.numdam.org/item/ITA_2001__35_6_551_0.pdf
- Definition 1.1 in Section 1; Theorem 2.1 in Section 2, printed page 554.
