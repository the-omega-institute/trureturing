---
bibkey: bugeaudkriegershallit2009morphic
authors: Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit
year: 2009
title: "Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation"
doi: null
url: https://arxiv.org/abs/0808.2544v2
claim: "Lemmas 10-12 and Corollary 13 give support stabilization and the predecessor/successor mechanism for sufficiently late and long maximal blocks in a morphic word, with bounded boundary corrections."
strata_touched:
  - D5/S1/Recurrence/Raney/MaximalBlockEvolution
  - D5/S1/Recurrence/Raney/MaximalBlockDescent
  - D5/S1/Recurrence/Raney/BoundaryPivotTransport
  - D5/S1/Recurrence/Raney/FinitePathDisplacements
license: citation-only
triage: anchor
---

# Morphic words and maximal blocks

## Verified locator

The primary source is arXiv:0808.2544v2 by Yann Bugeaud, Dalia Krieger, and
Jeffrey Shallit. Version 1 was submitted in August 2008 and version 2 in April
2009. The source is https://arxiv.org/abs/0808.2544v2. The relevant primary
body, not only the abstract or final limsup theorem, was read for this delivery.

## Attested mechanism

Lemma 10 replaces a morphism by a positive power for which the set of letters
reachable from each letter is stable under every further positive iterate.

Lemma 11 takes a sufficiently late and sufficiently long maximal block over a
chosen letter set. Its inverse-scale interval has a central block over that set,
while bounded neighborhoods at both ends contain complementary letters.

Lemma 12 runs the construction forward: after trimming bounded boundary
regions from a predecessor block, its morphic image remains inside the chosen
letter set and bounded image neighborhoods contain complementary letters.

Corollary 13 organizes sufficiently late and long maximal blocks into image
evolution sequences with bounded edge corrections. Bugeaud, Krieger, and
Shallit use this mechanism to obtain algebraic/rational information about a
limsup associated with maximal blocks.

## Repository boundary

The support-stabilizing power and the predecessor/successor mechanism are
literature prerequisites. The repository specializes them to uniform fixed
words and makes every endpoint condition explicit.

The following are repository adaptations and strengthening, not statements
attributed to the BKS abstract or its limsup conclusion: the boundary convention
at index zero; literal actual maximal intervals; finite descent chains and
their roots; finite families of early roots, late root words, and paired edge
contexts; deterministic paired pivot states; eventual periodicity of signed
left and right endpoint displacements; factorial normalization of those
periods; and one finite coefficient set covering every actual maximal block.
In particular, the source alone does not assert the repository endpoint that
all actual block lengths lie in finitely many affine prime-power families.
