---
bibkey: kauffman2026multivirtual
authors: Louis H. Kauffman, Sujoy Mukherjee, Petr Vojtěchovský
year: 2026
title: Algebraic invariants of multi-virtual links
doi: 10.1016/j.jalgebra.2026.03.018
url: https://arxiv.org/abs/2504.09368v1
claim: Problems 5.22 and 5.24 ask about maximal R-cliques in finite connected racks.
strata_touched:
  - D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations
license: citation-only
triage: anchor
---

# Maximal R-cliques in finite connected racks

The source is arXiv:2504.09368v1, submitted 2025-04-12. The journal
citation is Journal of Algebra 698 (2026), 493–532. Page numbers and
quotations below refer to the arXiv version; the journal full text was not
read, so equality of the journal problem numbering and wording is
ASSUMED-UNVERIFIED.

Printed page 13 states: “A magma (Q, ∗) is a right quasigroup if for every
x ∈ Q the right translation Rₓ is a permutation of Q.” It then states: “A right quasigroup (Q, ∗) is a rack if it satisfies
right self-distributivity (x ∗ y) ∗ z = (x ∗ z) ∗ (y ∗ z).”
Printed page 17 states: “Recall that a rack Q is connected if the
permutation group Mltr(Q) acts transitively on Q.” Printed page 18 states:
“A subset C of a right quasigroup Q is an R-clique if a ∼ b for every
a, b ∈ C.” Printed pages 17–18 also state: “Let ∼ be the binary relation on a right
quasigroup Q defined by a ∼ b if and only if [Ra, Rb] = 1.” “If a ∼ b, we
say that a and b R-commute.” Proposition 5.15 on printed page 19 states:
“Let Q be a rack and let C be a maximal R-clique of Q. Then C is a subrack
of Q.” Its proof uses “Since C is maximal, b ∈ C.” Maximality is therefore
with respect to inclusion.

Printed page 21 concludes section 5.5 with the following questions:

> Problem 5.22. Do all maximal R-cliques in a finite connected rack have the same size?

> Problem 5.23. Do maximal R-cliques in a finite connected rack Q partition Q?

> Problem 5.24. Does there exist a finite connected rack Q and a maximal R-clique C of Q such that |C| does not divide |Q|?

The paper's Example 5.11 on printed page 18 already answers Problem 5.23 negatively: ConnectedQuandle(10,1) has [R_0,R_1] = [R_1,R_3] = 1 but [R_0,R_3] ≠ 1, and maximal R-cliques partition a rack exactly when R-commutation is transitive. This delivery does not claim a settlement of Problem 5.23.

The formal refutations concern Problems 5.22 and 5.24 and use finite
conjugation racks: 105 fixed-point-free involutions in S₈ with maximal
R-cliques of sizes 7 and 9, and 70 three-cycles in S₇ with a maximal
R-clique of size 4. The latter refutes universal divisibility and answers
Problem 5.24 Yes. Problem 5.25 is outside these results.

A literature check reported on 2026-09-30 inspected the TeX sources of
five Semantic Scholar citing works (arXiv:2606.22501, 2606.01035,
2511.08045, 2506.16536, 2506.04437); none contained “clique” or the problem numbers 5.22 and 5.24. MathDB queries “maximal R-clique”, “R-clique rack”, and
“multi-virtual links” returned no entry for these problems. These are
bounded search results, not a claim that all literature was searched.

## Verified locator

- DOI: https://doi.org/10.1016/j.jalgebra.2026.03.018
- URL: https://arxiv.org/abs/2504.09368v1
- Source: https://arxiv.org/pdf/2504.09368v1, printed pages 13, 17–19, 21.
