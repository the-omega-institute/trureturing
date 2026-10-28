---
bibkey: popolishallitstipulanti2024additive
authors: Pierre Popoli and Jeffrey Shallit and Manon Stipulanti
year: 2024
title: Additive word complexity and Walnut
doi: 10.4230/LIPIcs.FSTTCS.2024.32
url: https://arxiv.org/abs/2410.02409v1
claim: Question 31 asks whether a natural valuation can make the additive complexity of a given infinite word equal its original-symbol abelian complexity at every length.
strata_touched:
  - D5/S1/Words/Complexity/PSSValuationRefutation
license: citation-only
triage: anchor
---

# Additive word complexity and Walnut

The source is arXiv:2410.02409v1, the authors' version with appendices of
the FSTTCS 2024 article. Section 2 defines an alphabet to be finite, an infinite
word to be indexed from zero, and a factor to be a contiguous subblock.
Definitions 1 and 3 identify additive equivalence at a fixed length with equality
of letter-value sums. Abelian equivalence is permutation of the original symbols,
equivalently equality of their Parikh vectors.

Section 5, PDF page 15, defines a valuation as any map `v : A → Nat` and asks:

> Given an alphabet A, is there a valuation such that the additive complexity
> of a given sequence is equal to its abelian complexity?

This is arXiv PDF Question 31 and official FSTTCS Question 31, printed page
32:14. The HTML rendition numbers it Question 30 in Section 4, at
`Thmtheorem30`. Theorem 32 in the PDF treats a relabeled Thue--Morse variant;
Theorem 33 treats C-balanced words. Those are restricted positive results,
not additional global hypotheses of the preceding question. The paragraph after
Lemma 6 also discusses concatenating all finite words, so words with a universal
factor language lie within the source setting.

The Lean definitions preserve the original alphabet when assigning natural
weights, including zero and repeated weights. They count finite images of the
actual factor set. The fixed counterexample enumerates finite ternary lists
and concatenates each with a zero separator. The cyclic triples `(b,c,a)` and
`(c,a,b)` have equal total count and equal scalar evaluation for weights
`(a,b,c)`; except for constant weights they are distinct. Constant weights
already identify distinct singleton classes. This is a repository derivation
answering the full general existence reading, rather than a theorem attributed
to the paper or an assertion about all individual infinite words.

## Verified locator

- Versioned arXiv record: https://arxiv.org/abs/2410.02409v1
- Versioned PDF: https://arxiv.org/pdf/2410.02409v1
- Versioned HTML question: https://arxiv.org/html/2410.02409v1#Thmtheorem30
- Official publication DOI: https://doi.org/10.4230/LIPIcs.FSTTCS.2024.32
- Official PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol323-fsttcs2024/LIPIcs.FSTTCS.2024.32/LIPIcs.FSTTCS.2024.32.pdf

The source HTML, arXiv PDF and official PDF support the same statement and
valuation definition. The cited text supplies the problem and definitions;
it does not supply the negative answer above. The bounded qualification search
found no exact posted settlement in the inspected sources; this is not a
worldwide absence or priority claim.
