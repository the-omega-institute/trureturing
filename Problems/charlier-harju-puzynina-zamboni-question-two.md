---
slug: charlier-harju-puzynina-zamboni-question-two
bibkey: charlier2015abelianbordered
doi: 10.48550/arXiv.1501.07464
url: https://arxiv.org/abs/1501.07464v1
triage: theorem
motivation_gids:
  - D5/S1/Words/AbelianBorders/AbelianBorderQuestion.result
---

# Weak Abelian Periodicity Does Not Force Finitely Many Weakly Abelian Unbordered Factors

## Problem

Émilie Charlier, Tero Harju, Svetlana Puzynina and Luca Q. Zamboni, *Abelian bordered factors and periodicity*,
arXiv:1501.07464v1, Section 7, Question 2: let w be an infinite bounded weakly abelian periodic word over a k-letter
alphabet such that its graph G_w belongs to a k-dimensional cylinder with axis with rational coefficients, and each
tangential line to G_w has points of G_w on it with bounded gaps. Does it follow that w has only finitely many weakly
abelian unbordered factors?

## Motivation

The theorem `D5/S1/Words/AbelianBorders/AbelianBorderQuestion.result` answers Question 2 negatively: an explicit word
over three letters satisfies all three hypotheses and has infinitely many weakly abelian unbordered factors.

## Gap

Pre-registration issue 13129 records the literature screen: the paper's Theorem 3 proves the forward implication and
the binary equal-frequency case of the converse, the citing literature and the 2023 survey of abelian combinatorics
on words do not settle Question 2, and the repository had no claim on it. This is a bounded negative finding.

## Route

1. With A = 110022222000111 and B = 012, the word w = B A^{e_1} B A^{e_2} … with unbounded exponents is a
   concatenation of blocks of length at most fifteen, all with letter frequencies (1/3, 1/3, 1/3), so it is bounded
   weakly abelian periodic.
2. Projecting prefix Parikh vectors by T(p) = (p₀ − p₂, p₁ − p₂), the path of A traces a quadrilateral and the only
   new state of B lies strictly inside it; hence the graph lies in a cylinder around the line t(1, 1, 1), the
   tangential lines are the four axis-parallel lines through the exposed vertices, and each is visited in every
   window of eighteen indices.
3. Each factor 12A^m0 starts and ends at the interior state, which is never an internal cut; the only chord through it
   joining two cut states forces equal prefix and suffix lengths, and the cut indices of its endpoints have the wrong
   residue modulo fifteen. Hence these factors are weakly abelian unbordered, and there are infinitely many of them.

## Falsifier

The refutation would fail if some factor 12A^m0 had a nonempty proper prefix and a nonempty suffix with equal letter
frequencies, or if some tangential line were visited only finitely often.

## Evidence

The proof seat and an independent referee implementation checked K = 3, 5 and 7 on long prefixes, including all
prefix and suffix pairs of the factors 12A^m0 for m ≤ 40, the cylinder radius and the tangential visit gaps.

## Triage

`theorem`; the statement is Question 2 of arXiv:1501.07464v1, answered negatively.

- Refuted (formalized): Question 2 has a negative answer over a three-letter alphabet.
- Proved (paper): the same construction works for every odd K ≥ 3 with A = 1²0²2^{K+2}0^K1^K.
- Open: Question 1 of the same paper (whether abelian bordered long factors force abelian periodicity).

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record of arXiv:1501.07464, its citing papers and the 2023 survey of
abelian combinatorics on words, web and GitHub searches and the repository checks.
