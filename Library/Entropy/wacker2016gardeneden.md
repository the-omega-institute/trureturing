---
bibkey: wacker2016gardeneden
authors: Simon Wacker
year: 2016
title: The Garden of Eden Theorem for Cellular Automata on Group Sets
doi: 10.1007/978-3-319-44365-2_7
url: https://arxiv.org/html/1603.07272v2
claim: Main Theorem 1 identifies surjectivity with finite-difference preinjectivity for cellular automata with finite alphabet and finite neighbourhood on right amenable left homogeneous spaces with finite stabilisers; Lemma 12 gives collar-controlled replacement and Theorem 6 gives strict image entropy loss from nonpreinjectivity.
strata_touched:
  - D5/S1/Dynamics/Symbolic/GardenOfEden
license: citation-only
triage: anchor
---

# Finite collars and the Garden-of-Eden theorem

The native specialization uses the additive group of integers, a finite
alphabet, and the forward neighborhood consisting of the integers from
zero through `k+1`. A configuration is an arbitrary function from the
integers to the alphabet. Preinjectivity means that two configurations
with the same complete image and a finite disagreement set are equal.

Main Theorem 1 includes empty and singleton alphabets. For larger
alphabets the proof compares the growth of actual image patterns with
the full alphabet growth. Lemma 12 permits replacement of colliding
patterns after retaining a collar wide enough to control every affected
local window. The proof of Theorem 6 repeats this replacement on disjoint
tiles and obtains strict image entropy loss.

For integer windows, a collision supported on `[a,b]` needs the collar
`[a-(k+1), b+(k+1)]`. A local output window touching the support is
contained in this collar. Disjoint words of length `m` can consequently
be normalized so that one of the `card(A)^m` blocks is absent, giving
the actual image-prefix bound

$$
  P(nm)\leq (|A|^m-1)^n |A|^{k+1}.
$$

The reverse implication uses compactness to obtain a missing finite
output word from nonsurjectivity. A missing word of length `m` gives
`P(nm) <= (card(A)^m-1)^n`. Preinjectivity supplies the opposing bound
`card(A)^n <= P(n+k+1)` by inserting arbitrary finite source words
into a constant ambient configuration. These counts concern spatial
prefixes of complete code images, rather than iterates of the code.

The native formalization is a specialization of this known theorem.
Only the mathematical statements and arguments are cited; no external
Lean source is copied. The last line of the Theorem 6 proof prints a
full-shift entropy expression; the theorem statement and preceding
argument concern image entropy.

## Verified locator

DOI: https://doi.org/10.1007/978-3-319-44365-2_7.
Primary version: https://arxiv.org/html/1603.07272v2.
The relevant locators are Main Theorem 1, Lemmas 10–12, and Theorems
4–6 in the PDF; the HTML rendering labels the latter three results
Theorems 4.1–4.3.
