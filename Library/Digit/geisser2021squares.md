---
bibkey: geisser2021squares
authors: Michael Geißer, Theresa Körner, Sascha Kurz and Anne Zahn
year: 2021
title: "Squares with three digits"
doi: null
url: https://arxiv.org/abs/2112.00444v2
claim: "If ⟨a₁′,...,aₗ′⟩ is a solution with l ≥ 2, then ⟨a₁′,...,aₗ₋₁′⟩ is also a solution."
strata_touched:
  - D5/S1/Digit/SquaresThreeDigitsPrefixRefutation
license: citation-only
triage: anchor
---

# Squares with three digits: prefix closure

## Verified locator

- URL: https://arxiv.org/abs/2112.00444v2
- Versioned text: https://arxiv.org/html/2112.00444v2#Thmconjecture1
- PDF: https://arxiv.org/pdf/2112.00444v2
- Locator: Section 3.3, decimal block shorthand on printed page 25 and
  Conjecture 1 on printed page 26; governing equations (24)–(27).
- Original version: https://arxiv.org/abs/2112.00444v1, Section 3.3,
  Conjecture 1, with the same block and deletion conventions.

The bibliographic year is the first submission year. Version 2 is the
revision of 10 January 2022; the versioned arXiv metadata identifies the
four authors listed above. Only short quotations and citations are retained.

Conjecture 1 states:

> If ⟨a₁′,...,aₗ′⟩ is a solution with l ≥ 2, then ⟨a₁′,...,aₗ₋₁′⟩ is also a solution.

Each entry is a nonnegative number of nines following a digit 4; concatenate
these blocks and append a final 5. A zero entry gives a lone 4. A solution
has every actual decimal digit of its ordinary integer square in {0,2,5}.
The notation expresses subset membership, not occurrence of all three digits.
The conjecture deletes the final whole block, retaining the final digit 5.

## Source and literature boundary

Both named versions state the same conjecture. The versioned v2 text and
arXiv metadata retain it as a conjecture. This source check establishes the
published question and its literal domain; it is not an exhaustive search
for subsequent resolutions. No worldwide openness, originality, priority or
historical solved-credit conclusion follows from this note.

The repository result is the literal negation of that universal implication,
with tuple [0,1,3,7,15,31,63,127,2,6,14,62,14,6,2]. Its definitions and proof
are in `D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.lean`; the formal
exposition is its owning Blueprint. No general carry classification,
least counterexample or assertion about other bases is attributed to it.
